import pytest

from kdrag import prove
from kdrag.smt import (
    BitVec,
    BitVecSort,
    BoolSort,
    Bools,
    CharVal,
    Concat,
    Const,
    Consts,
    DeclareSort,
    FPSort,
    FPs,
    If,
    Int,
    IntSort,
    Length,
    RNE,
    Real,
    RealSort,
    RealVal,
    SeqSort,
    String,
    StringVal,
    Unit,
    fpAdd,
)


@pytest.mark.parametrize(
    "sort",
    [
        IntSort(),
        RealSort(),
        BoolSort(),
        BitVecSort(8),
        FPSort(8, 24),
        DeclareSort("ConcatElement"),
        SeqSort(IntSort()),
    ],
)
def test_sequence_list_literals_and_element_errors(sort):
    x, y = Consts("x y", sort)
    xs = Const("xs", SeqSort(sort))
    assert ([x] + xs).eq(Concat(Unit(x), xs))
    assert (xs + [x]).eq(Concat(xs, Unit(x)))
    prove([x, y] + xs == Concat(Unit(x), Unit(y), xs))
    prove(xs + [x, y] == Concat(xs, Unit(x), Unit(y)))
    prove([] + xs == xs)
    prove(xs + [] == xs)
    with pytest.raises(TypeError, match=r"\[x\] \+ xs"):
        _ = x + xs
    with pytest.raises(TypeError, match=r"xs \+ \[x\]"):
        _ = xs + x


def test_python_values_coerce_to_the_element_sort():
    xs = Const("xs", SeqSort(RealSort()))
    prove(Length([1, 2] + xs) == 2 + Length(xs))
    prove(xs + [1] == Concat(xs, Unit(RealVal(1))))


def test_wrong_list_element_type_has_a_useful_error():
    xs = Const("xs", SeqSort(IntSort()))
    with pytest.raises(TypeError, match="list element 0 must have sort Int"):
        _ = [Real("wrong_sort")] + xs


def test_existing_sequence_and_string_concatenation():
    xs, ys = Consts("xs ys", SeqSort(IntSort()))
    assert (xs + ys).eq(Concat(xs, ys))
    s = String("s")
    assert (s + "end").eq(Concat(s, StringVal("end")))
    assert ("start" + s).eq(Concat(StringVal("start"), s))
    assert ([CharVal("a")] + s).eq(Concat(Unit(CharVal("a")), s))


def test_native_scalar_addition_still_works():
    x = Int("x")
    prove(x + 2 == 2 + x)
    r = Real("r")
    prove(r + 2 == 2 + r)
    b = BitVec("b", 8)
    prove(b + 2 == 2 + b)
    p, q = Bools("p q")
    assert (p + q).eq(If(p, 1, 0) + If(q, 1, 0))
    f, g = FPs("f g", FPSort(8, 24))
    assert (f + g).eq(fpAdd(RNE(), f, g))
