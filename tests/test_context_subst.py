import pytest

import kdrag.smt as smt
from kdrag.contrib.telescope import (
    Context,
    Hyp,
    ScopedExpr,
    Subst,
    Vars,
    prove,
    variables,
)


def test_context_prefixes_are_checked_objects_reused_by_identity():
    x, y = smt.Reals("context_x context_y")
    root = Context()
    bound = root.extend(Vars((x,)))
    assumed = bound.extend(Hyp(x > 0))
    assert assumed.prefix(1) is bound
    assert assumed.prefix(0) is root
    assert ScopedExpr(assumed, x).ctx is assumed
    with pytest.raises(ValueError, match="distinct"):
        assumed.extend(Vars((x,)))
    with pytest.raises(ValueError, match="later"):
        Context.of(Hyp(y > 0)).extend(Vars((y,)))
    with pytest.raises(TypeError, match="checked Context"):
        ScopedExpr((Vars((x,)),), x)


def test_forest_contains_terms_and_proofs_of_instantiated_hypotheses():
    (a,) = variables("forest_a", smt.RealSort())
    a = a.weaken((a > 1).assume())
    x = smt.Real("forest_x")
    dst = Context.of(Vars((x,)), Hyp(x > 0))
    positive = prove(a - 1 > 0)
    sigma = Subst(a.ctx, dst, ((a - 1,), positive))
    lemma = prove(x + 1 > 0, ctx=dst)
    result = sigma.apply(lemma)
    assert result.ctx is a.ctx
    assert result.thm.eq((a.raw - 1) + 1 > 0)
    with pytest.raises(TypeError, match="proofs"):
        Subst(a.ctx, dst, ((a - 1,), a - 1 > 0))
    with pytest.raises(ValueError, match="premise"):
        Subst(a.ctx, dst, ((a - 1,), prove(a == a)))


def test_forest_substitutions_compose_including_proof_components():
    (a,) = variables("compose_a", smt.RealSort())
    a = a.weaken((a > 1).assume())
    x, y = smt.Reals("compose_x compose_y")
    middle = Context.of(Vars((x,)), Hyp(x > 0))
    target = Context.of(Vars((y,)), Hyp(y > 1))
    sigma = Subst(a.ctx, middle, ((a - 1,), prove(a - 1 > 0)))
    sx = ScopedExpr(middle, x)
    tau = Subst(middle, target, ((sx + 1,), prove(sx + 1 > 1)))
    combined = sigma.then(tau)
    term = ScopedExpr(target, y * 2)
    assert combined.apply(term).raw.eq(sigma.apply(tau.apply(term)).raw)
    result = combined.apply(prove(y > 1, ctx=target))
    assert result.thm.eq((a.raw - 1) + 1 > 1)
    assert (
        sigma.then(Subst.identity(middle))
        .apply(ScopedExpr(middle, x))
        .raw.eq(a.raw - 1)
    )
    with pytest.raises(ValueError, match="mismatched"):
        tau.then(sigma)


def test_forest_preserves_simultaneous_blocks_and_checks_sorts():
    x, y = smt.Reals("block_x block_y")
    dst = Context.of(Vars((x, y)))
    (a,) = variables("block_a", smt.RealSort())
    sigma = Subst(a.ctx, dst, ((a, a + 1),))
    assert sigma.apply(ScopedExpr(dst, x - y)).raw.eq(a.raw - (a.raw + 1))
    with pytest.raises(ValueError, match="block"):
        Subst(a.ctx, dst, ((a,),))
    with pytest.raises(TypeError, match="sort"):
        Subst(a.ctx, dst, ((a, ScopedExpr(a.ctx, smt.IntVal(1))),))


def test_transport_does_not_capture_rigid_constants_in_payloads_or_contexts():
    (a,) = variables("rigid_a", smt.RealSort())
    sigma = Subst(a.ctx, Context(), ())
    with pytest.raises(ValueError, match="capture"):
        sigma.apply(ScopedExpr(Context(), a.raw))
    with pytest.raises(ValueError, match="capture"):
        sigma.apply(prove(a.raw == a.raw))
    rigid_hyp = Context.of(Hyp(a.raw > 0))
    conditional = a.weaken((a > 0).assume())
    with pytest.raises(ValueError, match="capture"):
        Subst(conditional.ctx, rigid_hyp, (prove(conditional > 0),))
