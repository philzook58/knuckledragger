import pytest

from kdrag import prove, seq, tuple_
from kdrag.smt import (
    Concat,
    Const,
    DeclareSort,
    Empty,
    IntSort,
    Real,
    RealSort,
    RealVal,
    SeqSort,
    Unit,
)
from kdrag.cast import cast, cast_table
from kdrag.solvers.symunion import py2expr


def test_contextual_sequence_cast_handles_empty_and_numeric_literals():
    sort = SeqSort(RealSort())
    assert cast(sort, []).eq(Empty(sort))
    prove(cast(sort, [1, 2]) == seq(RealVal(1), RealVal(2)))
    assert cast(sort, [1]).sort() == sort
    prove(cast(sort, [1, 2.5]) == seq(RealVal(1), RealVal("5/2")))


def test_nested_sequence_cast_uses_the_expected_inner_sort():
    inner = SeqSort(IntSort())
    outer = SeqSort(inner)
    prove(cast(outer, [[], [1]]) == Concat(Unit(Empty(inner)), Unit(seq(1))))


def test_custom_conversion_is_shared_by_direct_cast_and_concatenation(monkeypatch):
    sort = SeqSort(IntSort())
    xs = Const("xs", sort)
    replacement = seq(42)
    monkeypatch.setitem(cast_table, (sort, list), lambda _: replacement)
    assert cast(sort, [1]).eq(replacement)
    assert ([1] + xs).eq(Concat(replacement, xs))
    assert (xs + []).eq(Concat(xs, replacement))
    assert py2expr([1]).eq(replacement)


def test_custom_element_cast_is_used_inside_sequence_cast(monkeypatch):
    element = DeclareSort("CastTestElement")
    value = Const("value", element)
    monkeypatch.setitem(cast_table, (element, int), lambda _: value)
    assert cast(SeqSort(element), [1]).eq(Unit(value))


def test_inference_preserves_list_and_tuple_distinction():
    prove(py2expr([1, 2]) == seq(1, 2))
    assert py2expr((1, 2, 3)).eq(tuple_(1, 2, 3))
    prove(py2expr([(1, 2), (3, 4)]) == seq(tuple_(1, 2), tuple_(3, 4)))
    with pytest.raises(ValueError, match="empty list"):
        py2expr([])
    with pytest.raises(TypeError, match="explicit sequence cast"):
        py2expr([1, 2.5])


def test_bad_element_reports_the_position():
    with pytest.raises(TypeError, match="list element 1 must have sort Int"):
        cast(SeqSort(IntSort()), [1, Real("bad")])
