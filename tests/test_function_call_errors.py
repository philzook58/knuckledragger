import pytest

from kdrag import smt
from kdrag.smt import (
    ArraySort,
    BitVecSort,
    BitVecVal,
    BoolSort,
    Function,
    Int,
    IntSort,
    IntVal,
    Real,
    RealSort,
    StringVal,
)


def test_wrong_sort_identifies_declaration_and_argument():
    f = Function("diagnostic_f", IntSort(), RealSort(), BoolSort())
    with pytest.raises(smt.Z3Exception) as exc:
        f(Real("bad_real"), 42)
    message = str(exc.value)
    assert "(declare-fun diagnostic_f (Int Real) Bool)" in message
    assert "argument 1" in message
    assert "bad_real" in message
    assert "sort Real" in message
    assert "expected sort Int" in message
    assert isinstance(exc.value.__cause__, smt.Z3Exception)


def test_python_type_and_later_argument():
    f = Function("diagnostic_python", BoolSort(), IntSort(), BoolSort())
    with pytest.raises(smt.Z3Exception) as exc:
        f(True, "bad-number")
    message = str(exc.value)
    assert "diagnostic_python" in message
    assert "argument 2" in message
    assert "'bad-number'" in message
    assert "type str" in message
    assert "expected sort Int" in message


def test_z3_arithmetic_cast_attribute_error_gets_sort_diagnostic():
    f = Function("diagnostic_sequence", RealSort(), BoolSort())
    with pytest.raises(
        smt.Z3Exception, match=r"argument 1.*sort String.*expected sort Real"
    ) as exc:
        f(StringVal("bad-real"))
    # Some Z3 versions raise AttributeError rather than Z3Exception for this cast.
    assert isinstance(exc.value.__cause__, (smt.Z3Exception, AttributeError))


@pytest.mark.parametrize("container", [list, tuple])
def test_sequence_argument_form_is_diagnosed_after_unpacking(container):
    f = Function("diagnostic_packed", IntSort(), RealSort(), BoolSort())
    with pytest.raises(
        smt.Z3Exception, match=r"argument 2.*sort String.*expected sort Real"
    ):
        f(container([IntVal(1), StringVal("bad-real")]))


def test_bitvector_width_is_reported():
    f = Function("diagnostic_bv", BitVecSort(8), BoolSort())
    with pytest.raises(
        smt.Z3Exception, match=r"BitVec\(16\).*expected sort BitVec\(8\)"
    ):
        f(BitVecVal(1, 16))


def test_array_sorts_are_reported():
    f = Function("diagnostic_array", ArraySort(IntSort(), RealSort()), BoolSort())
    a = smt.Const("wrong_array", ArraySort(IntSort(), IntSort()))
    with pytest.raises(
        smt.Z3Exception, match=r"Array\(Int, Int\).*expected sort Array\(Int, Real\)"
    ):
        f(a)


def test_implicit_arguments_keep_declaration_positions():
    f = Function("diagnostic_implicit", IntSort(), RealSort(), BoolSort())
    f.implicits = ["index", None]
    with pytest.raises(
        smt.Z3Exception, match=r"argument 2.*sort String.*expected sort Real"
    ):
        f(StringVal("bad-real"))
    assert f(42).arg(1).sort() == RealSort()


def test_valid_coercions_and_subrange_are_preserved():
    f = Function("diagnostic_valid", RealSort(), RealSort())
    n = Int("coerced_int")
    assert f(42).arg(0).sort() == RealSort()
    assert f(n).arg(0).eq(smt.ToReal(n))
    assert f(smt.BoolVal(True)).arg(0).sort() == RealSort()
    f.subrange = lambda result: result >= 0
    result = f(42)
    assert result.assumes.eq(result >= 0)


def test_wrong_arity_still_raises_z3_exception():
    f = Function("diagnostic_arity", IntSort(), IntSort(), BoolSort())
    with pytest.raises(smt.Z3Exception, match="diagnostic_arity"):
        f(1)


def test_context_mismatch_identifies_argument():
    ctx = smt.Context()
    f = Function("diagnostic_context", IntSort(ctx), BoolSort(ctx))
    with pytest.raises(smt.Z3Exception, match="argument 1.*different Z3 context"):
        f(Int("foreign_argument"))
