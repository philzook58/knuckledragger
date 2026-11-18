import pytest

import kdrag as kd
import kdrag.smt as smt


@pytest.mark.parametrize(
    "sort",
    [
        smt.IntSort(),
        smt.RealSort(),
        smt.BoolSort(),
        smt.BitVecSort(8),
        smt.FPSort(8, 24),
        smt.DeclareSort("ConcatElement"),
        smt.SeqSort(smt.IntSort()),
    ],
)
def test_sequence_list_literals_and_element_errors(sort):
    x, y = smt.Consts("x y", sort)
    xs = smt.Const("xs", smt.SeqSort(sort))
    assert ([x] + xs).eq(smt.Concat(smt.Unit(x), xs))
    assert (xs + [x]).eq(smt.Concat(xs, smt.Unit(x)))
    kd.prove([x, y] + xs == smt.Concat(smt.Unit(x), smt.Unit(y), xs))
    kd.prove(xs + [x, y] == smt.Concat(xs, smt.Unit(x), smt.Unit(y)))
    kd.prove([] + xs == xs)
    kd.prove(xs + [] == xs)
    with pytest.raises(TypeError, match=r"\[x\] \+ xs"):
        _ = x + xs
    with pytest.raises(TypeError, match=r"xs \+ \[x\]"):
        _ = xs + x


def test_python_values_coerce_to_the_element_sort():
    xs = smt.Const("xs", smt.SeqSort(smt.RealSort()))
    kd.prove(smt.Length([1, 2] + xs) == 2 + smt.Length(xs))
    kd.prove(xs + [1] == smt.Concat(xs, smt.Unit(smt.RealVal(1))))


def test_wrong_list_element_type_has_a_useful_error():
    xs = smt.Const("xs", smt.SeqSort(smt.IntSort()))
    with pytest.raises(TypeError, match="list element 0 must have sort Int"):
        _ = [smt.Real("wrong_sort")] + xs


def test_existing_sequence_and_string_concatenation():
    xs, ys = smt.Consts("xs ys", smt.SeqSort(smt.IntSort()))
    assert (xs + ys).eq(smt.Concat(xs, ys))
    s = smt.String("s")
    assert (s + "end").eq(smt.Concat(s, smt.StringVal("end")))
    assert ("start" + s).eq(smt.Concat(smt.StringVal("start"), s))
    assert ([smt.CharVal("a")] + s).eq(smt.Concat(smt.Unit(smt.CharVal("a")), s))


def test_native_scalar_addition_still_works():
    x = smt.Int("x")
    kd.prove(x + 2 == 2 + x)
    r = smt.Real("r")
    kd.prove(r + 2 == 2 + r)
    b = smt.BitVec("b", 8)
    kd.prove(b + 2 == 2 + b)
    p, q = smt.Bools("p q")
    assert (p + q).eq(smt.If(p, 1, 0) + smt.If(q, 1, 0))
    f, g = smt.FPs("f g", smt.FPSort(8, 24))
    assert (f + g).eq(smt.fpAdd(smt.RNE(), f, g))
