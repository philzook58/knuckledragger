"""
Treating T -> Bool as a kind of truth value

- https://en.wikipedia.org/wiki/Modal_companion
- https://en.wikipedia.org/wiki/Modal_logic
- https://en.wikipedia.org/wiki/Boolean-valued_model
"""

import kdrag.smt as smt

"""
def FreshDom(doms):
    doms = smt.domains(p)
    xs = [smt.FreshConst(dom ,prefix=f"x{n}") for n,dom in enumerate(doms)] 
"""


def Box(p: smt.FuncRef) -> smt.QuantifierRef:
    """ """
    doms = smt.domains(p)
    xs = [smt.FreshConst(dom, prefix=f"x{n}") for n, dom in enumerate(doms)]
    x1s = [smt.FreshConst(dom, prefix=f"x{n}") for n, dom in enumerate(doms)]
    future = smt.And(
        [x <= x1 for x, x1 in zip(xs, x1s)] if len(xs) > 1 else xs[0] <= x1s[0]
    )
    return smt.Lambda(xs, smt.ForAll(x1s, future, p(*x1s)))


def Valid(p: smt.FuncRef) -> smt.BoolRef:
    """
    Convert from modal truth to regular Bool

    https://en.wikipedia.org/wiki/Validity_(logic)#Valid_formula
    """
    doms = smt.domains(p)
    xs = [smt.FreshConst(dom, prefix=f"x{n}") for n, dom in enumerate(doms)]
    return smt.ForAll(xs, p(*xs))


def PImplies(p, q):
    """
    Pointwise Implies
    """
    doms = smt.domains(p)
    xs = [smt.FreshConst(dom, prefix=f"x{n}") for n, dom in enumerate(doms)]
    # Todo: coerce.
    return smt.Lambda(xs, smt.Implies(p(*xs), q(*xs)))


def MImplies(p, q):
    """
    https://en.wikipedia.org/wiki/Modal_companion
    """
    return Box(PImplies(p, q))


def PointEq(x: smt.ExprRef, y) -> smt.ExprRef:
    """
    Pointwise equality rather than on the nose equality.

    >>> x = smt.Int("x")
    >>> PointEq(smt.Lambda([x], x), 1)
    Lambda(x0!..., x0!... == 1)
    """
    # Overloading Eq seems too violent as it already had a meaning
    if (
        isinstance(x, smt.QuantifierRef) or isinstance(x, smt.ArrayRef)
    ) and smt.is_func(x):
        doms = smt.domains(x)
        vs = [smt.FreshConst(d, prefix=f"x{n}") for n, d in enumerate(doms)]
        if isinstance(y, smt.ExprRef) and x.sort() == y.sort():
            return smt.Lambda(vs, PointEq(x(*vs), y(*vs)))
        else:
            # Try to lift y to x's domain
            return smt.Lambda(vs, PointEq(x(*vs), y))
    else:
        return smt.Eq(x, y)


PEq = PointEq


def coerce(s: smt.SortRef, e) -> smt.ExprRef:  # pointwise_cast? domain_cast?
    if isinstance(e, smt.ExprRef) and e.sort() == s:
        return e
    elif isinstance(s, smt.ArraySortRef):
        try:
            res = coerce(s.range(), e)
        except Exception as e:
            raise Exception("Cannot automatically coerce", e, s)
        vs = [smt.FreshConst(dom) for dom in smt.domains(s)]
        return smt.Lambda(vs, res)
    else:
        return s.cast(e)


def PointIf(c, t: smt.ExprRef, e: smt.ExprRef) -> smt.ExprRef:
    """
    Pointwise if-then-else rather than on the nose if-then-else.

    >>> x = smt.Int("x")
    >>> PointIf(smt.Lambda([x], x > 0), 1, -1)
    Lambda(x0!..., If(x0!... > 0, 1, -1))
    >>> PointIf(smt.Lambda([x], x > 0), smt.Lambda([x], x+1), -1)
    Lambda(x0!..., If(x0!... > 0, x0!... + 1, -1))
    """
    if not smt.is_func(c):
        raise Exception("Condition must be a function", c, c.sort())
    if isinstance(t, smt.ExprRef):
        tsort = t.sort()
        e = coerce(tsort, e)
    elif isinstance(e, smt.ExprRef):
        esort = e.sort()
        t = coerce(esort, t)
    doms = smt.domains(c)
    vs = [smt.FreshConst(d, prefix=f"x{n}") for n, d in enumerate(doms)]
    if smt.is_func(t):  # pass parameters into t and e
        return smt.Lambda(vs, smt.If(c(*vs), t(*vs), e(*vs)))
    else:  # lift constants
        return smt.Lambda(vs, smt.If(c(*vs), t, e))


PIf = PointIf
