import pytest

from kdrag import Lemma, prove
from kdrag import kernel, rewrite, smt, tactics, utils
from kdrag.smt import (
    BitVecSort,
    BitVecVal,
    Bool,
    BoolVal,
    Exists,
    ForAll,
    Implies,
    Int,
    IntSort,
    IntVal,
    Lambda,
    Real,
    RealSort,
    RealVal,
    ToReal,
)
from kdrag.theories.logic import axioms


@pytest.mark.parametrize(
    "rule", ["instan", "specialize", "forget", "rename_vars2", "rename_vars", "subst"]
)
def test_proof_rules_reject_wrong_sorts_before_substitution(rule):
    r = Real("checked_r")
    n = Int("checked_n")
    # Wrong-sort substitution used to leave r as a loose (:var 0).
    body = Implies(ForAll(n, n == n), r <= r)
    q = ForAll(r, body)
    pf = prove(q)
    with pytest.raises(TypeError, match=r"bound variable checked_r.*sort Real.*Int"):
        if rule == "instan":
            kernel.instan([IntVal(42)], pf)
        elif rule == "specialize":
            kernel.specialize([IntVal(42)], q)
        elif rule == "forget":
            kernel.forget([IntVal(42)], Exists(r, body))
        elif rule == "rename_vars2":
            kernel.rename_vars2(pf, [n])
        elif rule == "rename_vars":
            axioms.rename_vars(q, [n])
        else:
            tactics.subst(pf, [n], [n])


@pytest.mark.parametrize("value", [0, 42, 0.5])
def test_proof_call_casts_python_values_to_real_binders(value):
    r = Real("checked_call_r")
    n = Int("checked_call_n")
    premise = ForAll(n, n == n)
    pf = prove(ForAll(r, Implies(premise, r <= r)))
    expected = Implies(premise, RealVal(value) <= RealVal(value))
    assert pf(value).thm.eq(expected)
    with pytest.raises(TypeError, match="sort Real"):
        pf(IntVal(42))


def test_mixed_binders_use_binder_order_and_preserve_inner_quantifiers():
    r = Real("checked_mixed_r")
    n, m = Int("checked_mixed_n"), Int("checked_inner_m")
    b = Bool("checked_mixed_b")
    body = ForAll(m, Implies(b, r + ToReal(n) == ToReal(n) + r))
    pf = prove(ForAll([r, n, b], body))
    expected = ForAll(
        m,
        Implies(
            BoolVal(True),
            RealVal(42) + ToReal(IntVal(7)) == ToReal(IntVal(7)) + RealVal(42),
        ),
    )
    assert pf(42, 7, True).thm.eq(expected)
    assert kernel.instan([RealVal(42), IntVal(7), BoolVal(True)], pf).thm.eq(expected)
    with pytest.raises(TypeError, match=r"Term 2.*checked_mixed_n.*sort Int.*Real"):
        kernel.instan([RealVal(42), RealVal(7), BoolVal(True)], pf)


def test_arity_and_raw_python_terms_are_rejected_by_kernel():
    r = Real("checked_arity_r")
    q = ForAll(r, r == r)
    for ts in ([], [RealVal(1), RealVal(2)]):
        with pytest.raises(ValueError, match="Binder expects 1 terms"):
            kernel.instan(ts, prove(q))
    with pytest.raises(TypeError, match=r"sort Real.*int"):
        kernel.instan([42], prove(q))
    # Even an unused binder must be supplied a term of its declared sort.
    with pytest.raises(TypeError, match="sort Real"):
        kernel.specialize([IntVal(42)], ForAll(r, BoolVal(True)))
    b = smt.Const("checked_bv", BitVecSort(8))
    with pytest.raises(TypeError, match=r"BitVec\(8\).*BitVec\(16\)"):
        kernel.instan([BitVecVal(1, 16)], prove(ForAll(b, b == b)))


def test_lambda_calls_and_conversion_are_checked():
    r = Real("checked_lambda_r")
    n = Int("checked_lambda_n")
    lam = Lambda([r, n], r + ToReal(n))
    expected = RealVal(42) + ToReal(IntVal(7))
    assert lam(42, 7).eq(expected)
    assert rewrite.beta(lam[RealVal(42), IntVal(7)]).eq(expected)
    with pytest.raises(TypeError, match="sort Real"):
        lam(IntVal(42), IntVal(7))
    with pytest.raises(TypeError, match="sort Real"):
        axioms.beta_conv(lam, IntVal(42), IntVal(7))
    assert axioms.beta_conv(lam, RealVal(42), IntVal(7)).thm.arg(1).eq(expected)


def test_binder_opening_and_renaming_preserve_mixed_sorts():
    r = Real("checked_open_r")
    n = Int("checked_open_n")
    q = ForAll([r, n], r + ToReal(n) == ToReal(n) + r)
    for opener in [kernel.open_binder, utils.open_binder, utils.open_binder_unhygienic]:
        vs, body = opener(q)
        assert [v.sort() for v in vs] == [RealSort(), IntSort()]
        assert body.eq(vs[0] + ToReal(vs[1]) == ToReal(vs[1]) + vs[0])
    pf = prove(q)
    assert kernel.trigger(pf).thm.body().eq(q.body())
    assert (
        kernel.rename_vars2(pf, [Real("new_r"), Int("new_n")]).thm.body().eq(q.body())
    )
    assert utils.alpha_eq(utils.alpha_norm(q), q)


def test_tactic_specialize_casts_literal_and_failed_sort_check_preserves_state():
    r = Real("checked_tactic_r")
    rule = prove(ForAll(r, r <= r))
    l = Lemma(RealVal(42) <= RealVal(42))
    before = l.top_goal()
    with pytest.raises((TypeError, smt.Z3Exception)):
        l.specialize(rule, "not-real")
    assert l.top_goal() is before
    l.specialize(rule, 42)
    l.auto()
    l.qed()


@pytest.mark.parametrize("binder", [ForAll, Exists, Lambda])
def test_substitute_body_checks_quantifier_and_uses_binder_order(binder):
    r, n = Real("wrapper_r"), Int("wrapper_n")
    q = binder([r, n], r >= ToReal(n))
    result = smt.substitute_body(q, RealVal(42), IntVal(7))
    assert result.eq(RealVal(42) >= ToReal(IntVal(7)))
    with pytest.raises(TypeError, match=r"bound variable wrapper_r.*sort Real.*Int"):
        smt.substitute_body(q, IntVal(42), IntVal(7))
    with pytest.raises(ValueError, match="Binder expects 2 terms"):
        smt.substitute_body(q, RealVal(42))


def test_substitute_body_requires_a_quantifier_and_preserves_result_sort():
    with pytest.raises(TypeError, match="Expected QuantifierRef"):
        smt.substitute_body(IntVal(42), IntVal(7))
    r = Real("wrapper_result_r")
    assert smt.substitute_body(Lambda(r, r + 1), RealVal(42)).sort() == RealSort()


def test_alpha_norm_preserves_nested_binders_and_free_constants():
    r = Real("outer_r")
    n, m, free = Int("outer_n"), Int("inner_m"), Int("free_constant")
    for expr in [
        ForAll(n, Exists(m, n + m == free)),
        ForAll([r, n], Exists(m, r + ToReal(n + m) == ToReal(free))),
        Lambda(n, Lambda(m, n + m + free)),
    ]:
        assert utils.alpha_eq(utils.alpha_norm(expr), expr)
