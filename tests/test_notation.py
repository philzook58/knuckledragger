import operator
import subprocess
import sys

import pytest

import kdrag as kd
import kdrag.smt as smt
from kdrag import notation


SET_OPERATIONS = [
    (operator.or_, smt.SetUnion),
    (operator.and_, smt.SetIntersect),
    (operator.sub, smt.SetDifference),
    (operator.le, smt.IsSubset),
    (operator.ge, lambda s, t: smt.IsSubset(t, s)),
    (operator.lt, lambda s, t: smt.And(smt.IsSubset(s, t), s != t)),
    (operator.gt, lambda s, t: smt.And(smt.IsSubset(t, s), s != t)),
]


def test_set_defaults_without_theories_set():
    # Other test modules import theories.set during collection. Use a fresh
    # interpreter to verify that notation alone supplies the set operations.
    subprocess.run(
        [sys.executable, "-c", """
import sys
import kdrag
from kdrag.smt import *
S, T = Consts('S T', SetSort(RealSort()))
assert (S | T).eq(SetUnion(S, T))
assert (S & T).eq(SetIntersect(S, T))
assert (S - T).eq(SetDifference(S, T))
assert (~S).eq(SetComplement(S))
assert (S <= T).eq(IsSubset(S, T))
assert (S >= T).eq(IsSubset(T, S))
assert 'kdrag.theories.set' not in sys.modules
"""],
        check=True,
    )


@pytest.mark.parametrize("op, native", SET_OPERATIONS)
def test_raw_and_nested_sets(op, native):
    element = smt.DeclareSort("NotationSetElement")
    for sort in (smt.SetSort(element), smt.SetSort(smt.SetSort(element))):
        s, t = smt.Consts("s t", sort)
        assert op(s, t).eq(native(s, t))
        assert (~s).eq(smt.SetComplement(s))


@pytest.mark.parametrize("op, native", SET_OPERATIONS)
def test_set_sequences_lift_to_native_set_operations(op, native):
    element = smt.DeclareSort("NotationSequenceElement")
    set_sort = smt.SetSort(element)
    f, g = smt.Consts("f g", smt.ArraySort(smt.IntSort(), set_sort))
    i = smt.Int("i")
    result = op(f, g)
    assert smt.is_array_sort(result)
    assert result.sort().range() == native(f[i], g[i]).sort()
    kd.prove(result[i] == native(f[i], g[i]))
    kd.prove((~f)[i] == smt.SetComplement(f[i]))


def test_lambda_sets():
    x = smt.Real("x")
    s = smt.Lambda(x, x > 0)
    t = smt.Lambda(x, x < 1)
    assert (s | t).eq(smt.SetUnion(s, t))
    assert (s & t).eq(smt.SetIntersect(s, t))
    assert (~s).eq(smt.SetComplement(s))
    kd.prove((s | t)[x] == smt.Or(x > 0, x < 1))


def test_explicit_registration_overrides_set_default():
    sort = smt.SetSort(smt.DeclareSort("NotationOverrideElement"))
    s, t = smt.Consts("s t", sort)
    dispatch = notation.SortDispatch(
        name="custom_union", set_default=smt.SetUnion
    )
    dispatch.register(sort, lambda s, t: s)
    assert dispatch(s, t).eq(s)


def test_non_set_arrays_still_lift_pointwise():
    # The real-sequence theory registers subtraction on Int -> Real arrays.
    # Use a private index sort to exercise the fallback, not that override.
    index = smt.DeclareSort("NotationPointwiseIndex")
    f, g = smt.Consts("f g", smt.ArraySort(index, smt.RealSort()))
    i = smt.Const("i", index)
    kd.prove((f - g)[i] == f[i] - g[i])
    kd.prove((f <= g)[i] == (f[i] <= g[i]))

    # Multi-domain Boolean arrays are predicates, not Z3 sets.
    p, q = smt.Consts(
        "p q", smt.ArraySort(index, smt.RealSort(), smt.BoolSort())
    )
    x = smt.Real("x")
    kd.prove((p | q)[i, x] == smt.Or(p[i, x], q[i, x]))
    kd.prove((p & q)[i, x] == smt.And(p[i, x], q[i, x]))


def test_scalar_operations_still_work():
    p, q = smt.Bools("p q")
    assert (p | q).eq(smt.Or(p, q))
    assert (p & q).eq(smt.And(p, q))
    assert (~p).eq(smt.Not(p))
    x, y = smt.Reals("x y")
    kd.prove(x - y == x + -y)
    kd.prove((x <= y) == smt.Not(x > y))


def test_set_arithmetic_images():
    a, b = smt.Consts("a b", smt.SetSort(smt.RealSort()))
    x, y, z = smt.Reals("x y z")
    for op in (operator.add, operator.mul, operator.truediv):
        kd.prove(op(a, b)[z] == smt.Exists([x, y], a[x], b[y], z == op(x, y)))
    # The real-set theory explicitly overrides negation; exercise the fallback
    # on integer sets even when that theory was imported during collection.
    integers = smt.Const("integers", smt.SetSort(smt.IntSort()))
    n = smt.Int("n")
    kd.prove((-integers)[n] == integers[-n])
    kd.prove((a + 2)[z] == a[z - 2])
    kd.prove((2 + a)[z] == a[z - 2])
    kd.prove((2 * a)[z] == smt.Exists(x, a[x], z == 2 * x))
    # Repeated operands must still contribute independent witnesses.
    pair = smt.Lambda(x, smt.Or(x == 1, x == 2))
    kd.prove((pair + pair)[3])
    kd.prove(smt.Not((pair + pair)[5]))
    kd.prove((a + smt.EmptySet(smt.RealSort())) == smt.EmptySet(smt.RealSort()))


def test_set_lift_custom_operation_and_precedence():
    index = smt.DeclareSort("NotationImageElement")
    a = smt.Const("a", smt.SetSort(index))
    x = smt.Const("x", index)
    z = smt.Int("z")
    image = smt.Function("notation_image", index, smt.IntSort())
    dispatch = notation.SortDispatch(name="image")
    dispatch.register(index, image)
    kd.prove(dispatch(a)[z] == smt.Exists(x, a[x], z == image(x)))
    dispatch.register(a.sort(), lambda a: a)
    assert dispatch(a).eq(a)
    native = notation.SortDispatch(
        name="native_union", set_default=smt.SetUnion
    )
    assert native(a, a).eq(smt.SetUnion(a, a))


def test_automatic_lifting_defaults_and_errors():
    element = smt.DeclareSort("NotationAutomaticElement")
    a = smt.Const("a", smt.SetSort(element))
    f = smt.Const("f", smt.ArraySort(smt.IntSort(), element))
    for term in (a, f):
        default = notation.SortDispatch(name="default", default=lambda x: x)
        assert default(term).eq(term)
        factory = notation.SortDispatch(
            name="factory", default_factory=lambda sort: lambda x: x
        )
        assert factory(term).eq(term)
        # A missing scalar implementation should still terminate with its
        # normal error after peeling the surrounding set or array layer.
        with pytest.raises(NotImplementedError, match="NotationAutomaticElement"):
            notation.SortDispatch(name="missing")(term)
    # Generic dispatches lift predicates as images, not universal assertions.
    predicate = notation.SortDispatch(name="predicate")
    predicate.register(element, lambda x: smt.BoolVal(True))
    result = predicate(a)
    x = smt.Const("x", element)
    assert result.sort() == smt.SetSort(smt.BoolSort())
    kd.prove(result[True] == smt.Exists(x, a[x]))
    kd.prove(smt.Not(result[False]))


def test_image_with_multiple_sets_and_fixed_arguments():
    a, b, c = smt.Consts("a b c", smt.SetSort(smt.IntSort()))
    x, y, w, z, offset = smt.Ints("x y w z offset")
    image = notation.Image(lambda x, y, w, n: x + y + w + n, a, b, c, offset)
    kd.prove(image[z] == smt.Exists([x, y, w], a[x], b[y], c[w], z == x+y+w+offset))
    # Calling the helper directly also permits a symbolic scalar on the left.
    shifted = notation.Image(operator.add, offset, a)
    kd.prove(shifted[z] == a[z - offset])
    with pytest.raises(ValueError, match="at least one set operand"):
        notation.Image(operator.add, x, y)


def test_sequences_of_sets_lift_arithmetic():
    index = smt.DeclareSort("NotationImageIndex")
    set_sort = smt.SetSort(smt.IntSort())
    f, g = smt.Consts("f g", smt.ArraySort(index, set_sort))
    i = smt.Const("i", index)
    x, y, z = smt.Ints("x y z")
    kd.prove((f + g)[i][z] == smt.Exists([x, y], f[i][x], g[i][y], z == x + y))
