import pytest

import kdrag as kd
import kdrag.smt as smt
from kdrag.contrib.telescope import (
    Context,
    ScopedExpr,
    ScopedProof,
    lift,
    prove,
    variables,
)


def test_arithmetic_and_proving_carry_the_context():
    (x,) = variables("expr_x", smt.RealSort())
    result = prove(x + 0 == x)
    assert result.thm.eq(x.raw + 0 == x.raw)
    assert result.expr.raw.eq(result.thm)
    assert result.expr.ctx is result.ctx
    with pytest.raises(TypeError, match="Python booleans"):
        bool(x > 0)
    with pytest.raises(TypeError, match="Boolean proposition"):
        prove(x + 1)


def test_scoped_arguments_import_the_lemma_before_instantiation():
    x = smt.Real("lemma_x")
    lemma = ScopedProof.from_proof(kd.prove(smt.ForAll(x, x + 0 == x)))
    (a,) = variables("local_a", smt.RealSort())
    instance = lemma(a + 1)
    result = prove((a + 1) + 0 == a + 1, by=[instance])
    assert result.thm.eq((a.raw + 1) + 0 == a.raw + 1)
    assert not kd.kernel.is_fresh_var(a.raw)


def test_only_prefix_contexts_combine_and_raw_constants_stay_rigid():
    (x,) = variables("expr_x", smt.RealSort())
    (y,) = variables("expr_y", smt.RealSort(), ctx=x.ctx)
    assert (x + y).ctx is y.ctx
    (z,) = variables("unrelated_z", smt.RealSort())
    with pytest.raises(ValueError, match="prefix"):
        x + z
    with pytest.raises(ValueError, match="capture"):
        x + x.raw
    with pytest.raises(ValueError, match="capture"):
        ScopedExpr(Context.of(), y.raw).weaken(y.ctx)


def test_hypotheses_propagate_and_cannot_be_dropped():
    (x,) = variables("expr_x", smt.RealSort())
    conditional_x = x.weaken((x > 0).assume())
    result = prove(conditional_x + 1 > 0)
    with pytest.raises(ValueError, match="prefix"):
        prove(x + 1 > 0, by=[result])
    closed = result.expr.close().close()
    assert not closed.ctx
    assert closed.raw.eq(smt.ForAll(x.raw, x.raw > 0, x.raw + 1 > 0))
    with pytest.raises(kd.kernel.LemmaError):
        prove(x > 0)


def test_lambda_closing_is_different_from_closing_a_proposition():
    x, y = variables("expr_x expr_y", smt.RealSort())
    addition = (x + y).lambda_()
    assert addition.raw.num_vars() == 2
    assert not addition.ctx
    assert prove(addition[x, y] == x + y).thm.eq(
        addition.raw[x.raw, y.raw] == x.raw + y.raw
    )
    proposition = x > y
    assert proposition.close().raw.is_forall()
    assert proposition.lambda_().raw.is_lambda()
    assert not proposition.close().raw.eq(proposition.lambda_().raw)
    with pytest.raises(ValueError, match="Boolean"):
        (x + y).close()
    with pytest.raises(ValueError, match="hypothesis"):
        x.weaken((x > 0).assume()).lambda_()


def test_function_constructors_and_array_selection_preserve_context():
    (a,) = variables("parameter_a", smt.RealSort())
    (x,) = variables("bound_x", smt.RealSort(), ctx=a.ctx)
    constant = a.weaken(x.ctx).lambda_()
    assert constant.ctx == a.ctx
    assert prove(constant[a] == a).thm.eq(constant.raw[a.raw] == a.raw)
    f = smt.Function("scoped_f", smt.RealSort(), smt.RealSort())
    assert lift(f, a + 1).raw.eq(f(a.raw + 1))
    assert lift(f, a).ctx is a.ctx


def test_substitution_checks_the_scoped_terms_prefix():
    (x,) = variables("prefix_x", smt.RealSort())
    (y,) = variables("suffix_y", smt.RealSort(), ctx=x.ctx)
    source = prove(x + y == y + x)
    result = source.subst(1, (x + 1,))
    assert result.thm.eq(x.raw + (x.raw + 1) == (x.raw + 1) + x.raw)
    with pytest.raises(ValueError, match="prefix"):
        source.subst(0, (y,))
