import kdrag.smt as smt


cast_table = {}


def cast(s: smt.SortRef, e: object) -> smt.ExprRef:
    """Convert to an expected sort, honoring registered casts first.

    Lists cast to sequences recursively, including empty and nested lists.
    """
    if isinstance(e, smt.ExprRef):
        s1 = e.sort()
        if s1.eq(s):
            return e
        else:
            key = (s, e.sort())
    else:
        key = (s, type(e))
    coerce = cast_table.get(key)
    if coerce is not None:
        return coerce(e)
    elif isinstance(s, smt.SeqSortRef) and isinstance(e, list):
        units = []
        for i, value in enumerate(e):
            try:
                units.append(smt.Unit(cast(s.basis(), value)))
            except (smt.Z3Exception, TypeError) as error:
                raise TypeError(
                    f"Sequence cast: list element {i} must have sort {s.basis()}"
                ) from error
        if not units:
            return smt.Empty(s)
        if len(units) == 1:
            return units[0]
        return smt.Concat(*units)
    else:
        # if isinstance(e, smt.SeqRef):
        # elif isinstance(e, smt.ArraySortRef):
        return s.cast(e)


def cast_dt(dt: smt.DatatypeSortRef, e: smt.DatatypeRef) -> smt.DatatypeRef:
    """
    Simple field name based downcasting between two struct-like datatypes

    """
    dt1 = e.sort()
    assert dt1.num_constructors() == 1 and dt.num_constructors() == 1
    constr, constr1 = dt.constructor(0), dt1.constructor(0)
    assert constr.arity() <= constr1.arity()
    args = []
    for i in range(constr.arity()):
        acc = dt.accessor(0, i)
        args.append(getattr(e, acc.name()))  # TODO:  consider extra cast here
    return constr(*args)


"""
def coerce_exprs(a, b):
    return smt._coerce_exprs(a, b)


def coerce_expr_merge(s: smt.SortRef, a: smt.ExprRef):
    return smt._coerce_expr_merge(s, a)
"""


def subsort(s: smt.SortRef, t: smt.SortRef) -> bool:
    return s.subsort(t)
