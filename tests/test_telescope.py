import pytest

import kdrag as kd
import kdrag.smt as smt
from kdrag.contrib.telescope import Hyp, ScopedProof, Vars, internalize, prove


def test_mixed_context_preserves_order_and_binder_blocks():
    x, y, z = smt.Reals("x y z")
    ctx = (Vars((x, y)), Hyp(x > 0), Vars((z,)), Hyp(z > x))
    expected = smt.RawForAll(
        [x, y], smt.Implies(x > 0, smt.RawForAll(z, smt.Implies(z > x, z > 0)))
    )
    pf = prove(z > 0, ctx=ctx)
    assert pf.to_expr().eq(expected)
    assert not internalize((Vars((x, y)),), x == y).eq(
        internalize((Vars((x,)), Vars((y,))), x == y)
    )


def test_open_close_with_named_locals_preserves_certificate():
    x, y, a, b = smt.Reals("x y a b")
    original = kd.prove(smt.ForAll([x, y], x > y, x + 1 > y))
    pf = ScopedProof.from_proof(original).fix((a, b)).intro()
    assert pf.thm.eq(a + 1 > b)
    assert pf.ctx[1].thm.eq(a > b)
    assert not kd.kernel.is_fresh_var(a)
    closed = pf.close().close()
    assert closed.ctx == ()
    assert kd.utils.alpha_eq(closed.thm, original.thm)
    assert closed.closed is original


def test_shared_context_and_closed_definition_alignment():
    x, y = smt.Reals("x y")
    twice = kd.define("telescope_test_twice", [y], y + y)
    ctx = (Vars((x,)), Hyp(x > 0))
    positive = prove(x > 0, ctx=ctx)
    result = prove(twice(x) > 0, ctx=ctx, by=[positive, twice.defn])
    assert result.close().close().thm.eq(smt.ForAll(x, x > 0, twice(x) > 0))


def test_weakening_cannot_capture_existing_rigid_constants():
    x = smt.Real("x")
    pf = ScopedProof.from_proof(kd.prove(x == x))
    with pytest.raises(ValueError, match="capture"):
        pf.weaken((Vars((x,)),))
    with pytest.raises(ValueError, match="capture"):
        prove(x == x, ctx=(Vars((x,)),), by=[pf])


def test_fix_cannot_capture_a_free_constant_or_rebind_a_local():
    x, c = smt.Reals("x c")
    pf = ScopedProof.from_proof(kd.prove(smt.ForAll(x, x + c == c + x)))
    with pytest.raises(ValueError, match="capture"):
        pf.fix((c,))
    pf = prove(smt.ForAll(c, c == c), ctx=(Vars((x,)),))
    with pytest.raises(ValueError, match="distinct"):
        pf.fix((x,))


def test_context_reconciliation_rejects_reordering_and_different_hypotheses():
    x, y = smt.Reals("x y")
    pf = prove(x > 0, ctx=(Vars((x,)), Hyp(x > 0)))
    with pytest.raises(ValueError, match="prefix"):
        prove(x > 0, ctx=(Vars((x,)), Hyp(x > 1)), by=[pf])
    with pytest.raises(ValueError, match="later"):
        prove(x > 0, ctx=(Hyp(x > 0), Vars((x,))))
    pf = prove(x + y == y + x, ctx=(Vars((x,)), Vars((y,))))
    with pytest.raises(ValueError, match="prefix"):
        pf.weaken((Vars((y,)), Vars((x,))))


def test_substitution_updates_suffix_hypotheses_and_uses_only_prefix_terms():
    x, y = smt.Reals("x y")
    ctx = (Vars((x,)), Hyp(x > 0), Vars((y,)), Hyp(y > x))
    pf = prove(y > 0, ctx=ctx)
    instantiated = pf.subst(0, (smt.RealVal(2),))
    assert instantiated.ctx[0].thm.eq(smt.RealVal(2) > 0)
    assert instantiated.ctx[2].thm.eq(y > 2)
    assert instantiated.thm.eq(y > 0)
    at_prefix = pf.subst(2, (x + 1,))
    assert at_prefix.ctx[-1].thm.eq(x + 1 > x)
    assert at_prefix.thm.eq(x + 1 > 0)
    with pytest.raises(ValueError, match="later"):
        pf.subst(0, (y,))
    with pytest.raises(ValueError, match="later"):
        pf.subst(0, (x + 1,))


def test_substitution_preserves_multiargument_block_boundary():
    x, y = smt.Reals("x y")
    pf = prove(x + y == y + x, ctx=(Vars((x, y)),))
    with pytest.raises(ValueError, match="count"):
        pf.subst(0, (smt.RealVal(1),))
    result = pf.subst(0, (smt.RealVal(1), smt.RealVal(2)))
    assert result.ctx == ()
    assert result.thm.eq(smt.RealVal(1) + 2 == smt.RealVal(2) + 1)


def test_metadata_alone_cannot_change_a_proven_judgment():
    x = smt.Real("x")
    certificate = kd.prove(x == x)
    with pytest.raises(ValueError, match="Certificate"):
        ScopedProof((Vars((x,)),), x > 0, certificate)
    with pytest.raises(kd.kernel.LemmaError):
        prove(x > 0, ctx=(Vars((x,)),))


def test_lemma_instantiation_with_local_variables_in_by():
    x, a = smt.Reals("lemma_x local_a")
    lemma = kd.prove(smt.ForAll(x, x + 0 == x))
    ctx = (Vars((a,)),)
    # Instantiating first loses the distinction between a local and a rigid a.
    with pytest.raises(ValueError, match="capture"):
        prove(a + 0 == a, ctx=ctx, by=[lemma(a)])
    local_lemma = ScopedProof.from_proof(lemma, ctx)
    instance = local_lemma(a)
    result = prove(a + 0 == a, ctx=ctx, by=[instance])
    assert result.thm.eq(a + 0 == a)
    assert not kd.kernel.is_fresh_var(a)


def test_natural_proof_application_with_a_local_premise():
    x, a = smt.Reals("lemma_x local_a")
    lemma = kd.prove(smt.ForAll(x, x > 0, x + 1 > 0))
    ctx = (Vars((a,)), Hyp(a > 0))
    positive = prove(a > 0, ctx=ctx)
    result = ScopedProof.from_proof(lemma, ctx)(a, positive)
    assert result.thm.eq(a + 1 > 0)
    assert result.close().close().thm.eq(smt.ForAll(a, a > 0, a + 1 > 0))
    with pytest.raises(ValueError, match="premise"):
        ScopedProof.from_proof(lemma, ctx)(a, prove(a == a, ctx=ctx))


def test_contextual_application_does_not_turn_a_false_premise_into_a_theorem():
    x, a = smt.Reals("lemma_x local_a")
    ctx = (Vars((a,)),)
    lemma = kd.prove(smt.ForAll(x, x > 0, x + 1 > 0))
    with pytest.raises(TypeError, match="proofs"):
        ScopedProof.from_proof(lemma, ctx)(a, a > 0)
    with pytest.raises(TypeError, match="sort"):
        ScopedProof.from_proof(lemma, ctx)(smt.IntVal(1))
    with pytest.raises(ValueError, match="prefix"):
        wrong_context = prove(a > 0, ctx=ctx + (Hyp(a > 0),))
        ScopedProof.from_proof(lemma, ctx)(a, wrong_context)


def test_named_roundtrip_can_be_reused_in_another_variable_context():
    x, y, a, b, c = smt.Reals("x y a b c")
    source = kd.prove(smt.ForAll(x, smt.ForAll(y, x + y == y + x)))
    renamed = ScopedProof.from_proof(source).fix((a,)).fix((b,)).close().close()
    local = renamed.weaken((Vars((c,)),))
    result = local(c)
    assert kd.utils.alpha_eq(result.thm, smt.ForAll(b, c + b == b + c))
