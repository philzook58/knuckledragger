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
        name="custom_union", pointwise=True, set_default=smt.SetUnion
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
