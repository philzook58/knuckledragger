import kdrag.smt as smt
import kdrag as kd

type SubSort = smt.QuantifierRef | smt.ArrayRef
type Telescope = list[
    tuple[smt.ExprRef, smt.BoolRef] | tuple[smt.ExprRef, SubSort] | smt.ExprRef
]


def TForAll(xs: Telescope, P: smt.BoolRef) -> smt.BoolRef:
    """
    Dependent forall quantifier for a telescope of variables.
    Kind of like a proof irrelevant Pi type.

    Subtype / Refinement style usage

    >>> x, y, z = smt.Reals("x y z")
    >>> TForAll([(x, x > 0), (y, y > x)], y > -1)
    ForAll(x, Implies(x > 0, ForAll(y, Implies(y > x, y > -1))))

    "Dependent type" style usage

    >>> Pos = smt.Lambda([x], x > 0)
    >>> GT = lambda x: smt.Lambda([y], y > x)
    >>> TForAll([(x, Pos), (y, GT(x))], y > -1)
    ForAll(x, Implies(x > 0, ForAll(y, Implies(y > x, y > -1))))
    """
    for v in reversed(xs):
        if isinstance(v, tuple):
            (v, T) = v
            if T.sort() == smt.BoolSort():
                P = kd.QForAll([v], T, P)
            elif isinstance(T, smt.ArrayRef) or (
                isinstance(T, smt.QuantifierRef) and T.is_lambda()
            ):
                P = kd.QForAll([v], T(v), P)
            else:
                raise TypeError(f"Unsupported type for quantifier: {T}")
        else:
            P = kd.QForAll([v], P)
    return P


def TExists(xs: Telescope, P: smt.BoolRef) -> smt.BoolRef:
    """
    Dependent exists quantifier for a telescope of variables.
    Kind of like a proof irrelevant Sigma type.

    Subtype / Refinement style usage

    >>> x, y, z = smt.Reals("x y z")
    >>> TExists([(x, x > 0), (y, y > x)], y > -1)
    Exists(x, And(x > 0, Exists(y, And(y > x, y > -1))))

    "Dependent type" style usage

    >>> Pos = smt.Lambda([x], x > 0)
    >>> GT = lambda x: smt.Lambda([y], y > x)
    >>> TExists([(x, Pos), (y, GT(x))], y > -1)
    Exists(x, And(x > 0, Exists(y, And(y > x, y > -1))))
    """
    for v in reversed(xs):
        if isinstance(v, tuple):
            (v, T) = v
            if T.sort() == smt.BoolSort():
                P = kd.QExists([v], T, P)
            elif isinstance(T, smt.ArrayRef) or (
                isinstance(T, smt.QuantifierRef) and T.is_lambda()
            ):
                P = kd.QExists([v], T(v), P)
            else:
                raise TypeError(f"Unsupported type for quantifier: {T}")
        else:
            P = kd.QExists([v], P)
    return P
