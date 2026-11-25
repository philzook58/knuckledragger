import pytest

import kdrag as kd
from kdrag.smt import And, Bool, BoolVal, Implies, Int


def test_focus_exports_only_the_completed_claim():
    x = Int("x")
    l = kd.Lemma(x >= 0, assumes=[x > 0])
    claim = l.have(x >= 1)
    with l:
        assert not l.lemmas[-1]
        intermediate = l.have(x > -1, by=[])
        l.auto()
    assert len(l.lemmas[-1]) == 1
    assert l.ctx[-1].eq(claim)
    assert not any(h.eq(intermediate) for h in l.ctx)
    l.auto()
    l.qed()


def test_unfinished_focus_restores_goal_and_siblings():
    l = kd.Lemma(And(BoolVal(True), BoolVal(True)))
    l.split()
    original = l.top_goal()
    original_goals = l.goals.copy()
    with pytest.raises(ValueError, match="Unfinished focused proof"):
        with l:
            l.have(BoolVal(True), by=[])
    assert l.top_goal() is original
    assert all(a is b for a, b in zip(l.goals, original_goals, strict=True))
    assert not l.lemmas[-1]
    with l:
        l.auto()
    with l:
        l.auto()
    l.qed()


def test_exception_after_closing_focus_leaves_parent_goal_open():
    l = kd.Lemma(BoolVal(True))
    original = l.top_goal()
    with pytest.raises(RuntimeError, match="stop"):
        with l:
            l.auto()
            raise RuntimeError("stop")
    assert l.top_goal() is original
    assert not l.lemmas[-1]


def test_nested_focus():
    x = Int("x")
    l = kd.Lemma(x - x == 0)
    with l:
        l.cases(x < 0, x >= 0)
        with l.case(x < 0):
            l.auto()
        with l.case(x >= 0):
            l.auto()
    assert not l.goals
    assert l.qed().thm.eq(x - x == 0)


def test_scope_reuses_exact_target_proof_at_exit(monkeypatch):
    target = BoolVal(True)
    l = kd.Lemma(target)
    proof = kd.prove(target)

    def unexpected_solver_call(*args, **kwargs):
        raise AssertionError("an exact target proof is already available")

    monkeypatch.setattr(kd.kernel, "prove", unexpected_solver_call)
    with l:
        l.exact(proof)
    assert l.qed() is proof


def test_scope_can_reconstruct_an_assumption_proof():
    p = Bool("p")
    target = Implies(p, p)
    l = kd.Lemma(target)
    with l:
        l.intro()
        l.assumption()
    assert l.qed().thm.eq(target)
