"""
Theory of fixed point arithmetic
"""

import kdrag as kd
from kdrag import NewType
import kdrag.smt as smt
from kdrag.smt import BV2Int, BitVecSort, Consts, RealVal, ToReal
import functools

# https://pmc.ncbi.nlm.nih.gov/articles/PMC7324132/ An SMT Theory of Fixed-Point Arithmetic
# https://www.why3.org/stdlib/mach.fxp.html


@functools.cache
def FixedSort(bvsize: int, exp: int) -> smt.DatatypeSortRef:
    """

    >>> FixedSort(64, 0)
    Fixed_64_0
    """
    # put exp into record or make part of sort?
    S = NewType(f"Fixed_{bvsize}_{exp}", BitVecSort(bvsize))
    x, y, z = Consts("x y z", S)
    kd.notation.to_real.define(
        [x], ToReal(BV2Int(x.val, is_signed=True)) * RealVal(2) ** exp
    )
    S.exp = exp
    return S
