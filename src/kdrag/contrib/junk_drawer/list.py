"""
Algebraic datatype of lists.

You may prefer using theories.seq which offers more builtin support for things like associativity.
"""

import kdrag as kd
import kdrag.smt as smt


def Cons(x: smt.ExprRef, xs: smt.DatatypeRef) -> smt.DatatypeRef:
    """
    Helper to construct Cons values
    >>> Cons(1, Nil(smt.IntSort()))
    Cons(1, Nil)
    """
    LT = kd.ListSort(smt._py2expr(x).sort())
    return LT.Cons(x, xs)


def Nil(sort: smt.SortRef) -> smt.DatatypeRef:
    """
    Helper to construct Nil values
    >>> Nil(smt.IntSort())
    Nil
    """
    return kd.ListSort(sort).Nil


def Unit(x: smt.ExprRef) -> smt.DatatypeRef:
    """
    Helper to create Unit values
    >>> Unit(42)
    Cons(42, Nil)
    >>> Unit(42).sort()
    List_Int
    """
    x = smt._py2expr(x)
    LT = kd.ListSort(x.sort())
    return LT.Cons(x, LT.Nil)
