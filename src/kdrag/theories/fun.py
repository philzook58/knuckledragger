# import kdrag as kd
import kdrag.smt as smt


def MultiStore(a: smt.ArrayRef, addr: smt.ExprRef, *vs: smt.ExprRef) -> smt.ArrayRef:
    """
    >>> a = smt.Array('a', smt.IntSort(), smt.IntSort())
    >>> MultiStore(a, 42, 1,2,3)
    Store(Store(Store(a, 42, 1), 43, 2), 44, 3)
    """
    for n, v in enumerate(vs):
        a = smt.Store(a, addr + n, v)  # type: ignore
    return a


def store_view(
    a: smt.ArrayRef,
) -> tuple[smt.ArrayRef, list[tuple[smt.ExprRef, smt.ExprRef]]]:
    """
    Strips off the stores from an array and returns the base array and a list of (index, value) pairs.

    >>> a = smt.Array('a', smt.IntSort(), smt.IntSort())
    >>> b = MultiStore(a, 42, 1,2,3)
    >>> store_view(b)
    (a, [(42, 1), (43, 2), (44, 3)])
    """
    stores = []
    while smt.is_store(a):
        a, i, v = a.children()
        stores.append((i, v))
    return a, list(reversed(stores))
