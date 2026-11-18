import pytest

import kdrag as kd
import kdrag.smt as smt
from kdrag.cast import cast, cast_table
from kdrag.solvers.symunion import py2expr


def test_contextual_sequence_cast_handles_empty_and_numeric_literals():
    sort = smt.SeqSort(smt.RealSort())
    assert cast(sort, []).eq(smt.Empty(sort))
    kd.prove(cast(sort, [1, 2]) == kd.seq(smt.RealVal(1), smt.RealVal(2)))
    assert cast(sort, [1]).sort() == sort
    kd.prove(cast(sort, [1, 2.5]) == kd.seq(smt.RealVal(1), smt.RealVal("5/2")))


def test_nested_sequence_cast_uses_the_expected_inner_sort():
    inner = smt.SeqSort(smt.IntSort())
    outer = smt.SeqSort(inner)
    kd.prove(
        cast(outer, [[], [1]])
        == smt.Concat(smt.Unit(smt.Empty(inner)), smt.Unit(kd.seq(1)))
    )


def test_custom_conversion_is_shared_by_direct_cast_and_concatenation(monkeypatch):
    sort = smt.SeqSort(smt.IntSort())
    xs = smt.Const("xs", sort)
    replacement = kd.seq(42)
    monkeypatch.setitem(cast_table, (sort, list), lambda _: replacement)
    assert cast(sort, [1]).eq(replacement)
    assert ([1] + xs).eq(smt.Concat(replacement, xs))
    assert (xs + []).eq(smt.Concat(xs, replacement))
    assert py2expr([1]).eq(replacement)


def test_custom_element_cast_is_used_inside_sequence_cast(monkeypatch):
    element = smt.DeclareSort("CastTestElement")
    value = smt.Const("value", element)
    monkeypatch.setitem(cast_table, (element, int), lambda _: value)
    assert cast(smt.SeqSort(element), [1]).eq(smt.Unit(value))


def test_inference_preserves_list_and_tuple_distinction():
    kd.prove(py2expr([1, 2]) == kd.seq(1, 2))
    assert py2expr((1, 2, 3)).eq(kd.tuple_(1, 2, 3))
    kd.prove(py2expr([(1, 2), (3, 4)]) == kd.seq(kd.tuple_(1, 2), kd.tuple_(3, 4)))
    with pytest.raises(ValueError, match="empty list"):
        py2expr([])
    with pytest.raises(TypeError, match="explicit sequence cast"):
        py2expr([1, 2.5])


def test_bad_element_reports_the_position():
    with pytest.raises(TypeError, match="list element 1 must have sort Int"):
        cast(smt.SeqSort(smt.IntSort()), [1, smt.Real("bad")])
