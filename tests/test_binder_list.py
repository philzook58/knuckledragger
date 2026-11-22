import pytest

import kdrag as kd
from kdrag import smt


def test_binder_list_entry_points_agree(monkeypatch):
    x, y, z = kd.FreshVars("x y z", smt.IntSort())
    binders = [x, y, z]
    h1, h2, conclusion = x <= y, y <= z, x <= z

    @kd.Theorem(binders, h1, h2, conclusion)
    def transitive(l):
        """An example with two premises."""
        assert all(a is b for a, b in zip(l.top_goal().sig, binders, strict=True))
        assert l.ctx[0].eq(h1) and l.ctx[1].eq(h2)
        assert l.goal.eq(conclusion)
        l.auto()

    direct = kd.prove(binders, h1, h2, conclusion, solver="z3", by=[])
    expected = smt.ForAll(binders, h1, h2, conclusion)
    assert transitive.thm.eq(expected)
    assert direct.thm.eq(expected)
    assert transitive.__doc__ == "An example with two premises."
    zero, one, two = map(smt.IntVal, range(3))
    assert direct(zero, one, two, kd.prove(zero <= one), kd.prove(one <= two)).thm.eq(
        zero <= two
    )
    open_proof = kd.prove(smt.Implies(h1, smt.Implies(h2, conclusion)))
    a, b, c = smt.Ints("a b c")
    renamed = kd.prove(smt.ForAll([a, b, c], a <= b, b <= c, a <= c))

    def unexpected_solver(*args, **kwargs):
        pytest.fail("exact must be solver-free")

    monkeypatch.setattr(kd.kernel, "prove", unexpected_solver)
    assert kd.exact(binders, h1, h2, conclusion, open_proof).thm.eq(expected)
    assert kd.exact(binders, h1, h2, conclusion, pf=renamed) is renamed
    with pytest.raises(ValueError, match="Exact theorem mismatch"):
        kd.exact(binders, h1, h2, z <= x, open_proof)


def test_header_intros_stop_at_conclusion_and_keep_guards():
    x = kd.FreshVar("x", smt.IntSort())
    y = smt.Int("y")
    x.assumes = x >= 0
    premise = smt.And(x <= 1, x >= 0)
    conclusion = smt.Implies(x > 0, smt.ForAll([y], x + y > y))

    @kd.Theorem([x], premise, conclusion)
    def positive(l):
        assert len(l.ctx) == 2
        assert l.ctx[0].eq(x.assumes)
        assert l.ctx[1].eq(premise)
        assert l.goal.eq(conclusion)
        l.intro()
        assert l.goal.is_forall()
        l.auto()

    assert positive.thm.eq(smt.ForAll([x], premise, conclusion))
    assert kd.prove([x], premise, conclusion).thm.eq(positive.thm)


def test_quantified_conclusion_is_the_initial_goal():
    x = kd.FreshVar("x", smt.IntSort())
    y = smt.Int("y")
    conclusion = smt.ForAll([y], x + y == y + x)

    @kd.Theorem([x], conclusion)
    def commute(l):
        assert l.ctx == []
        assert l.goal.eq(conclusion)
        l.auto()

    assert commute.thm.eq(smt.ForAll([x], conclusion))


def test_prove_forwards_supporting_lemmas_and_solver_options():
    x = kd.FreshVar("x", smt.IntSort())
    succ = kd.define("binder_list_test_successor", [x], x + 1)
    conclusion = succ(x) > x
    proof = kd.prove([x], conclusion, by=succ.defn, solver="z3", timeout=2000)
    assert proof.thm.eq(smt.ForAll([x], conclusion))
    with pytest.raises(kd.kernel.SolverFailure):
        kd.prove([x], conclusion, solver="z3", timeout=2000)


@pytest.mark.parametrize("entrypoint", [kd.Theorem, kd.PTheorem, kd.prove, kd.exact])
def test_invalid_binder_list_headers(entrypoint):
    x = kd.FreshVar("x", smt.IntSort())
    truth = smt.BoolVal(True)
    proof = kd.prove(truth)

    def call(binders, *formulas):
        if entrypoint is kd.exact:
            return entrypoint(binders, *formulas, proof)
        return entrypoint(binders, *formulas)

    with pytest.raises(ValueError, match="nonempty"):
        call([], truth)
    with pytest.raises(TypeError, match="FreshVar"):
        call([smt.Int("ordinary")], truth)
    with pytest.raises(ValueError, match="distinct"):
        call([x, x], truth)
    with pytest.raises(TypeError, match="conclusion"):
        call([x])
    with pytest.raises(TypeError, match="Boolean"):
        call([x], x)


def test_theorem_preview(capsys):
    x = kd.FreshVar("x", smt.IntSort())

    @kd.PTheorem([x], x > 0, x >= 1)
    def unfinished(l):
        assert l.ctx[0].eq(x > 0)
        assert l.goal.eq(x >= 1)

    assert "Next Goal:" in capsys.readouterr().out

    @kd.PTheorem([x], x > 0, x < 0)
    def impossible(l):
        l.auto()

    failure = capsys.readouterr().out
    assert "auto failed in impossible" in failure
    assert "Solver found a countermodel." in failure

    @kd.PTheorem([x], x == x)
    def done(l):
        l.auto()

    assert "Lemma Complete!" in capsys.readouterr().out


def test_legacy_calls_and_list_form_timing(capsys):
    x = kd.FreshVar("x", smt.IntSort())
    truth = smt.BoolVal(True)
    expected = kd.prove(smt.ForAll([x], truth, truth))
    assert kd.exact(thm=expected.thm, pf=expected) is expected
    assert kd.exact(expected.thm, expected) is expected

    def solve(l):
        l.auto()

    assert kd.Theorem(truth, True)(solve).thm.eq(truth)
    assert kd.Theorem(goal=truth, timing=True)(solve).thm.eq(truth)
    assert kd.Theorem([x], truth, timing=True)(solve).thm.eq(smt.ForAll([x], truth))
    assert capsys.readouterr().out.count("Starting theorem solve") == 3
