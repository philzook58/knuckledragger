"""
Disjoint unions: A + B = A × {0} ∪ B × {1}, with tags inl(x) = (x, 0) and
inr(y) = (y, 1). Used for ordinal sums (Halmos §21) and cardinal sums (§24).
"""

from kdrag import Theorem, define
from kdrag.smt import And, Consts, ForAll, Or
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import ZFSet, elem, pair, prod, sing, zero
from kdrag.contrib.zf.fun import pair_elem_prod, pfst, pfst_pair
from kdrag.contrib.zf.nat import one

A, B, p = Consts("A B p", ZFSet)

osum_set = define("osum_set", [A, B], (prod(A, sing(zero))) | (prod(B, sing(one))))


@Theorem(
    ForAll(
        [A, B, p],
        elem(p, osum_set(A, B))
        == Or(
            And(elem(pfst(p), A), p == pair(pfst(p), zero)),
            And(elem(pfst(p), B), p == pair(pfst(p), one)),
        ),
    )
)
def elem_osum_set(l):
    """The elements of A + B are (x, 0) with x ∈ A and (y, 1) with y ∈ B."""
    A, B, p0 = l.fixes()
    l.unfold(osum_set)
    l.rw(zf.elem_union)
    l.split()
    # → : p ∈ A × {0} is (x, z) with z = 0, and pfst recovers x.
    l.intro()
    l.auto(by=[zf.elem_prod_def, zf.elem_sing, pfst_pair])
    l.intro()
    l.auto(by=[pair_elem_prod, zf.elem_sing])


def inl(x):
    return pair(x, zero)


def inr(x):
    return pair(x, one)
