import kdrag as kd
import functools
import kdrag.smt as smt


@functools.cache
def List(sort: smt.SortRef):
    """
    Build List sort
    >>> IntList = List(smt.IntSort())
    >>> IntList.Cons(1, IntList.Nil)
    Cons(1, Nil)
    """
    dt = kd.Inductive("List_" + sort.name())
    dt.declare("Nil")
    dt.declare("Cons", ("head", sort), ("tail", dt))
    return dt.create()


def list(*args):
    """
    Helper to construct List values
    >>> list(1, 2, 3)
    Cons(1, Cons(2, Cons(3, Nil)))
    """
    if len(args) == 0:
        raise ValueError("list() requires at least one argument")
    LT = List(smt._py2expr(args[0]).sort())
    acc = LT.Nil
    for a in reversed(args):
        acc = LT.Cons(a, acc)
    return acc


def Cons(x, xs):
    """
    Helper to construct Cons values
    >>> Cons(1, Nil(smt.IntSort()))
    Cons(1, Nil)
    """
    LT = List(smt._py2expr(x).sort())
    return LT.Cons(x, xs)


def Nil(sort: smt.SortRef) -> smt.DatatypeRef:
    """
    Helper to construct Nil values
    >>> Nil(smt.IntSort())
    Nil
    """
    return List(sort).Nil


def Unit(x: smt.ExprRef) -> smt.DatatypeRef:
    """
    Helper to create Unit values
    >>> Unit(42)
    Cons(42, Nil)
    >>> Unit(42).sort()
    List_Int
    """
    x = smt._py2expr(x)
    LT = List(x.sort())
    return LT.Cons(x, LT.Nil)
