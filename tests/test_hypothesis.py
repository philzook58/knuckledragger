from hypothesis  import strategies as st
from hypothesis import given
import kdrag as kd
import kdrag.smt as smt
import kdrag.hypothesis as hyp
import pytest

import kdrag.theories.nat as nat
import kdrag.theories.list as list_

import kdrag.reflect as reflect

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

def test_forall1():
    x = smt.Int("x")
    hyp.nitpick(smt.ForAll([x], x > x - 1))
    with pytest.raises(Exception) as _:
        hyp.nitpick(smt.ForAll([x], x < 0)) 
    z = smt.String("z")
    hyp.nitpick(smt.ForAll([z,x], smt.And( smt.Or(z == "foo", z != "foo") , smt.Or(x > 0, x == 0, x < 0))))
    n,m = smt.Consts("n m", nat.Nat)
    hyp.nitpick(smt.ForAll([n,m], n + m == m + n))
    with pytest.raises(Exception) as _:
        hyp.nitpick(smt.ForAll([n], n + nat.Z == n + nat.one))
    hyp.nitpick(smt.ForAll([n,m], smt.Or(n.is_Z, n.is_S)))
    l = smt.Const("l", list_.List(smt.IntSort()))
    hyp.nitpick(smt.ForAll([l], smt.Or(l == list_.Nil(smt.IntSort()), l.is_Cons)))


@given(hyp.smt_sorts)
def test_reflect_sort(s):
    assert reflect.sort_of_type(reflect.type_of_sort(s)) == s