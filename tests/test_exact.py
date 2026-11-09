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
