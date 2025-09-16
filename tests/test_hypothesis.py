from hypothesis  import strategies as st
from hypothesis import given
import kdrag as kd
import kdrag.smt as smt
import kdrag.hypothesis as hyp
import pytest

import kdrag.theories.nat as nat
import kdrag.theories.list as list_

import kdrag.reflect as reflect

@pytest.mark.slow
@given(hyp.smt_sorts)
def test_smt_sorts(s : smt.SortRef):
    assert isinstance(s, smt.SortRef)


@pytest.mark.slow
@given(hyp.smt_sorts.flatmap(lambda s: hyp.val_of_sort(s).map(lambda v: (s ,v))))
def test_val_of_sort(sv):
    s, v = sv
    assert v.sort() == s


@pytest.mark.slow
@given(hyp.smt_sorts.flatmap(lambda s: hyp.smt_generic_val(s).map(lambda v: (s ,v))))
def test_generic_val(sb):
    s, v = sb
    assert v.sort() == s

"""
@given(hyp.val_of_sort(nat.Nat))
def test_datatype_nat(n):  
    assert n.eq(nat.Z)

@given(hyp.val_of_sort(list_.List(smt.IntSort())))
def test_datatype_list(n):  
    assert n.eq(list_.Nil(smt.IntSort())
"""

@pytest.mark.slow
def test_forall1():
    x = smt.Int("x")
    hyp.quickcheck(smt.ForAll([x], x > x - 1))
    with pytest.raises(Exception) as _:
        hyp.quickcheck(smt.ForAll([x], x < 0)) 
    z = smt.String("z")
    hyp.quickcheck(smt.ForAll([z,x], smt.And( smt.Or(z == "foo", z != "foo") , smt.Or(x > 0, x == 0, x < 0))))
    n,m = smt.Consts("n m", nat.Nat)
    hyp.quickcheck(smt.ForAll([n,m], n + m == m + n))
    with pytest.raises(Exception) as _:
        hyp.quickcheck(smt.ForAll([n], n + nat.Z == n + nat.one))
    hyp.quickcheck(smt.ForAll([n,m], smt.Or(n.is_Z, n.is_S)))
    IntList = list_.List(smt.IntSort())
    l = smt.Const("l", IntList.T)
    hyp.quickcheck(smt.ForAll([l], smt.Or(l == IntList.Nil, l.is_Cons)))


@pytest.mark.slow
@given(hyp.smt_sorts)
def test_reflect_sort(s):
    assert reflect.sort_of_type(reflect.type_of_sort(s)) == s

@pytest.mark.slow
@given(hyp.smt_bool_expr)
def test_bool_expr(e):
    assert e.sort() == smt.BoolSort()

@pytest.mark.slow
@given(hyp.smt_int_expr)
def test_int_expr(e):
    assert e.sort() == smt.IntSort()