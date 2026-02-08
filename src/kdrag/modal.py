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

# TODO: could be smart about variable domain name choice by inheriting it from the inputs if they all share the same name.
Then accidental capture can't happen.

"""
type PBoolRef = smt.FuncRef
type PExprRef = smt.FuncRef


def Next(p: PBoolRef, prefix="t") -> PBoolRef:
    """
    >>> t = smt.Const("t", smt.IntSort())
    >>> Next(smt.Lambda([t], t))
    Lambda(t!..., t!... + 1)
    """
    doms = smt.domains(p)
    assert len(doms) == 1
    t = smt.FreshConst(doms[0], prefix=prefix)
    return smt.Lambda([t], p(t + 1))


def Box(p: PBoolRef, prefix="t") -> PBoolRef:
    """ """
    doms = smt.domains(p)
    if len(doms) == 1:
        x = smt.FreshConst(doms[0], prefix=prefix)
        x1 = smt.FreshConst(doms[0], prefix=prefix + "1")
        future = x <= x1
        return smt.Lambda([x], smt.ForAll([x1], future, p(x1)))
    else:
        xs = [smt.FreshConst(dom, prefix=f"{prefix}{n}") for n, dom in enumerate(doms)]
        x1s = [smt.FreshConst(dom, prefix=f"{prefix}{n}") for n, dom in enumerate(doms)]
        future = smt.And(
            [x <= x1 for x, x1 in zip(xs, x1s)] if len(xs) > 1 else xs[0] <= x1s[0]
        )
        return smt.Lambda(xs, smt.ForAll(x1s, future, p(*x1s)))


def Valid(p: PBoolRef, prefix="t") -> smt.BoolRef:
    """
    Convert from modal truth to regular Bool

    https://en.wikipedia.org/wiki/Validity_(logic)#Valid_formula

    >>> t = smt.Const("t", smt.IntSort())
    >>> Valid(Box(smt.Lambda([t], t > 0)))
    ForAll(t!..., ForAll(t1!..., Implies(t!... <= t1!..., t1!... > 0)))
    """
    doms = smt.domains(p)
    if len(doms) == 1:
        x = smt.FreshConst(doms[0], prefix=prefix)
        return smt.ForAll([x], p(x))
    else:
        xs = [smt.FreshConst(dom, prefix=f"{prefix}{n}") for n, dom in enumerate(doms)]
        return smt.ForAll(xs, p(*xs))


def PImplies(p: PBoolRef, q: PBoolRef, prefix="t") -> PBoolRef:
    """
    Pointwise Implies

    >>> t = smt.Const("t", smt.IntSort())
    >>> PImplies(smt.Lambda([t], t > 0), smt.Lambda([t], t > 1))
    Lambda(t!..., Implies(t!... > 0, t!... > 1))
    """
    doms = smt.domains(p)
    xs = [smt.FreshConst(dom, prefix=prefix) for dom in doms]
    # Todo: coerce.
    return smt.Lambda(xs, smt.Implies(p(*xs), q(*xs)))


def PAnd(*args, prefix="t") -> PBoolRef:
    """
    Pointwise And

    >>> t = smt.Const("t", smt.IntSort())
    >>> PAnd(smt.Lambda([t], t > 0), smt.Lambda([t], t < 10))
    Lambda(t!..., And(t!... > 0, t!... < 10))
    """
    doms = smt.domains(args[0])
    xs = [smt.FreshConst(dom, prefix=prefix) for dom in doms]
    return smt.Lambda(xs, smt.And(*(a(*xs) for a in args)))


def POr(*args, prefix="t") -> PBoolRef:
    """
    Pointwise Or

    >>> t = smt.Const("t", smt.IntSort())
    >>> POr(smt.Lambda([t], t > 0), smt.Lambda([t], t < 10))
    Lambda(t!..., Or(t!... > 0, t!... < 10))
    """
    doms = smt.domains(args[0])
    xs = [smt.FreshConst(dom, prefix=prefix) for dom in doms]
    return smt.Lambda(xs, smt.Or(*(a(*xs) for a in args)))


def MImplies(p: PBoolRef, q: PBoolRef) -> PBoolRef:
    """

    https://en.wikipedia.org/wiki/Modal_companion
    """
    return Box(PImplies(p, q))


def PointEq(x: PExprRef, y: PExprRef) -> PBoolRef:
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
            return smt.Lambda(vs, smt.Eq(x(*vs), y(*vs)))
        else:
            # Try to lift y to x's domain
            return smt.Lambda(vs, smt.Eq(x(*vs), y))
    else:
        raise TypeError("PointEq only supports functions and arrays for now", x, y)


PEq = PointEq


def PDistinct(*args, prefix="t") -> PBoolRef:
    """
    Pointwise Distinct

    >>> t = smt.Const("t", smt.IntSort())
    >>> PDistinct(smt.Lambda([t], t), smt.Lambda([t], t + 1))
    Lambda(t!..., t!...  != t!... + 1)
    """

    doms = smt.domains(args[0])
    vs = [smt.FreshConst(d, prefix=prefix) for d in doms]
    return smt.Lambda(vs, smt.Distinct(*(a(*vs) for a in args)))


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


def In(x: PExprRef, S: smt.FuncRef, prefix="t") -> PBoolRef:
    """
    >>> x = smt.Array("x", smt.IntSort(), smt.IntSort())
    >>> S = smt.Array("S", smt.IntSort(), smt.SetSort(smt.IntSort()))
    >>> In(x, S)
    Lambda(t!..., S[t!...][x[t!...]])
    """
    doms = smt.domains(S)
    vs = [smt.FreshConst(d, prefix=prefix) for n, d in enumerate(doms)]
    return smt.Lambda(vs, S[*vs][x(*vs)])
