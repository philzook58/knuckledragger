import pytest

import kdrag as kd
import kdrag.smt as smt


def test_exact_returns_matching_proof_unchanged():
    x = smt.Int("exact_x")
    pf = kd.prove(x == x)
    assert kd.exact(x == x, pf) is pf


def test_exact_infers_nested_universal_arguments():
    x, y = smt.Ints("exact_x exact_y")
    pf = kd.prove(smt.ForAll(x, smt.ForAll(y, x + y == y + x)))
    target = smt.IntVal(2) + 3 == smt.IntVal(3) + 2
    result = kd.exact(target, pf)
    assert result.thm.eq(target)
    assert pf.thm.is_forall()


def test_exact_accepts_bound_variable_renaming():
    x, y, z = smt.Ints("exact_x exact_y exact_z")
    pf = kd.prove(smt.ForAll(x, x == x))
    assert kd.exact(smt.ForAll(y, y == y), pf) is pf
    pf = kd.prove(smt.ForAll(x, smt.Lambda(y, x + y) == smt.Lambda(y, y + x)))
    target = smt.Lambda(z, 2 + z) == smt.Lambda(z, z + 2)
    assert kd.utils.alpha_eq(kd.exact(target, pf).thm, target)


def test_exact_does_not_substitute_free_constants_or_discharge_premises():
    x, y = smt.Ints("exact_x exact_y")
    p = smt.Bool("exact_p")
    with pytest.raises(ValueError, match="mismatch"):
        kd.exact(y == y, kd.prove(x == x))
    with pytest.raises(ValueError, match="mismatch"):
        kd.exact(p, kd.prove(smt.Implies(p, p)))


def test_exact_rejects_undetermined_arguments():
    x = smt.Int("exact_x")
    with pytest.raises(ValueError, match="mismatch"):
        kd.exact(smt.BoolVal(True), kd.prove(smt.ForAll(x, smt.BoolVal(True))))


@pytest.mark.parametrize("quantified", [False, True])
@pytest.mark.parametrize("count", [1, 3])
def test_exact_rejects_different_conjunction_arity(quantified, count):
    x = smt.Int("exact_x")
    source = smt.And(x == x, smt.BoolVal(True))
    pf = kd.prove(smt.ForAll(x, source) if quantified else source)
    target_x = smt.IntVal(1) if quantified else x
    target = smt.And(
        [target_x == target_x]
        + ([smt.BoolVal(True), smt.BoolVal(False)] if count == 3 else [])
    )
    with pytest.raises(ValueError, match="mismatch"):
        kd.exact(target, pf)


@pytest.mark.parametrize("with_context", [False, True])
def test_exact_tactic_infers_arguments(with_context):
    x = smt.Int("exact_tactic_x")
    p = smt.Bool("exact_tactic_p")
    body = x + 0 == x
    target = smt.IntVal(2) + 0 == 2
    if with_context:
        body, target = smt.Implies(p, body), smt.Implies(p, target)
    pf = kd.prove(smt.ForAll(x, body))
    l = kd.Lemma(target)
    if with_context:
        l.intros()
    assert l.exact(pf).is_empty()
    assert l.qed().thm.eq(target)


def test_exact_tactic_accepts_binder_renaming():
    x, y = smt.Ints("exact_tactic_x exact_tactic_y")
    pf = kd.prove(smt.ForAll(x, x == x))
    l = kd.Lemma(smt.ForAll(y, y == y))
    assert l.exact(pf).is_empty()


def test_exact_tactic_mismatch_preserves_state():
    p = smt.Bool("exact_tactic_p")
    l = kd.Lemma(p)
    before = l.top_goal()
    lemmas = dict(l.lemmas[-1])
    with pytest.raises(ValueError, match="mismatch"):
        l.exact(kd.prove(smt.BoolVal(True)))
    assert l.top_goal() == before
    assert l.lemmas[-1] == lemmas
