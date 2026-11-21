import pytest

from kdrag import smt
from kdrag.smt import (
    BitVecSort,
    BitVecVal,
    BoolSort,
    Function,
    Int,
    IntSort,
    Real,
    RealSort,
)


def test_call_error_shows_declaration_and_typed_arguments():
    f = Function("diagnostic_f", IntSort(), RealSort(), BoolSort())
    with pytest.raises(smt.Z3Exception) as exc:
        f(Real("bad_real"), 42)
    message = str(exc.value)
    assert "(declare-fun diagnostic_f (Int Real) Bool)" in message
    assert "arguments [bad_real (Real), 42 (int)]" in message
    assert isinstance(exc.value.__cause__, smt.Z3Exception)
    assert str(exc.value.__cause__) in message


def test_python_type_and_later_argument():
    f = Function("diagnostic_python", BoolSort(), IntSort(), BoolSort())
    with pytest.raises(smt.Z3Exception) as exc:
        f(True, "bad-number")
    message = str(exc.value)
    assert "diagnostic_python (Bool Int) Bool" in message
    assert "arguments [True (bool), 'bad-number' (str)]" in message


@pytest.mark.parametrize("wrong_arity", [False, True])
def test_detailed_native_errors_are_unchanged(wrong_arity):
    f = Function("diagnostic_bv", BitVecSort(8), BoolSort())
    args = () if wrong_arity else (BitVecVal(1, 16),)
    with pytest.raises(smt.Z3Exception) as original:
        smt.old_call(f, *args)
    with pytest.raises(smt.Z3Exception) as exc:
        f(*args)
    assert str(exc.value) == str(original.value)
    assert exc.value.__cause__ is None


def test_valid_coercions_and_implicit_arguments_are_preserved():
    f = Function("diagnostic_valid", RealSort(), RealSort())
    n = Int("coerced_int")
    assert f(42).arg(0).sort() == RealSort()
    assert f(n).arg(0).eq(smt.ToReal(n))
    g = Function("diagnostic_implicit", IntSort(), RealSort(), BoolSort())
    g.implicits = ["index", None]
    assert g(42).arg(1).sort() == RealSort()
