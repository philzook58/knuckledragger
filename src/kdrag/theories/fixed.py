"""
Theory of fixed point arithmetic
"""

import kdrag as kd
import kdrag.smt as smt
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
    S = kd.NewType(f"Fixed_{bvsize}_{exp}", smt.BitVecSort(bvsize))
    x, y, z = smt.Consts("x y z", S)
    kd.notation.to_real.define(
        [x], smt.ToReal(smt.BV2Int(x.val, is_signed=True)) * smt.RealVal(2) ** exp
    )
    S.exp = exp  # type: ignore
    return S
