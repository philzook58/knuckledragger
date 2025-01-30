import kdrag as kd
import kdrag.smt as smt
import functools
import operator


def lift_unop(S, op):
    def res(x):
        t = smt.FreshInt("t")
        return S(smt.Lambda([t], op(x.val)))

    return res


def lift_binop(S, op):
    def res(x, y):
        assert x.sort() == S
        y1 = smt._py2expr(y)
        if y1.sort() != S:
            y1 = TLift(y1)
            if y1.sort() != S:
                raise TypeError(f"{y} but expected sort {S}")
        assert isinstance(y1, smt.DatatypeRef)
        t = smt.FreshInt("t")
        return S(smt.Lambda([t], op(x.val[t], y1.val[t])))

    return res


def Not(x: smt.DatatypeRef) -> smt.DatatypeRef:
    """
    >>> x = smt.Const("x", TSort(smt.BoolSort()))
    >>> smt.simplify(Valid(Not(x)))
    Not(val(x)[0])
    """
    t = smt.FreshInt("t")
    S = TSort(smt.BoolSort())
    return S(smt.Lambda([t], smt.Not(x.val[t])))


@functools.cache
def TSort(sort):
    """
    Lift a sort to a sort that depends on time

    >>> TR = TSort(smt.RealSort())
    >>> x,y = smt.Consts("x y", TR)
    >>> _ = x + y
    >>> _ = x + 2.1
    """
    S = kd.NewType(f"T_{sort.name()}", smt.ArraySort(smt.IntSort(), sort))
    kd.notation.add.register(S, lift_binop(S, operator.add))
    kd.notation.sub.register(S, lift_binop(S, operator.sub))
    kd.notation.mul.register(S, lift_binop(S, operator.mul))
    kd.notation.div.register(S, lift_binop(S, operator.truediv))
    kd.notation.and_.register(S, lift_binop(S, operator.and_))
    kd.notation.or_.register(S, lift_binop(S, operator.or_))
    kd.notation.invert.register(S, Not)
    return S

    # kd.notation.eq.register(S, lift(operator.eq))


TBool = TSort(smt.BoolSort())
TInt = TSort(smt.IntSort())
TReal = TSort(smt.RealSort())
TString = TSort(smt.StringSort())


def TLift(n: smt.ExprRef | int | str) -> smt.DatatypeRef:
    """
    Lift a value into a constant signal

    >>> TLift(1)
    T_Int(K(Int, 1))
    >>> TLift(True)
    T_Bool(K(Int, True))
    """
    n = smt._py2expr(n)
    return TSort(n.sort())(smt.K(smt.IntSort(), n))


def And(*args):
    """
    >>> _ = And(TLift(True), TLift(False))
    """
    assert all(x.sort() == TBool for x in args)
    if len(args) == 0:
        return TLift(smt.BoolVal(True))
    elif len(args) == 1:
        return args[0]
    return functools.reduce(operator.and_, args)


def Or(*args):
    """

    >>> _ = Or(TLift(True), TLift(False))
    """
    assert all(x.sort() == TBool for x in args)
    if len(args) == 0:
        return TLift(smt.BoolVal(False))
    elif len(args) == 1:
        return args[0]
    return functools.reduce(operator.or_, args)


def Next(x):
    """

    >>> x = smt.Const("x", TSort(smt.BoolSort()))
    >>> Next(x)
    T_Bool(Lambda(t!..., val(x)[t!... + 1]))
    """
    t = smt.FreshInt("t")
    S = x.sort()
    return S(smt.Lambda([t], x.val[t + 1]))


def X(p):
    return Next(p)


def Always(x):
    assert x.sort() == TBool
    t = smt.FreshInt("t")
    dt = smt.FreshInt("dt")
    S = x.sort()
    return S(smt.Lambda([t], kd.QForAll([dt], dt >= 0, x.val[t + dt])))


def G(x):
    return Always(x)


def Eventually(x):
    assert x.sort() == TBool
    t = smt.FreshInt("t")
    dt = smt.FreshInt("dt")
    S = x.sort()
    return S(smt.Lambda([t], kd.QExists([dt], dt >= 0, x.val[t + dt])))


def F(x):
    return Eventually(x)


def If(c: smt.DatatypeRef, x: smt.DatatypeRef, y: smt.DatatypeRef) -> smt.DatatypeRef:
    """
    >>> _ = If(TLift(True), TLift(1), TLift(2))
    """
    t = smt.FreshInt("t")
    assert x.sort() == y.sort()
    assert c.sort() == TBool
    S = x.sort()
    return S(smt.Lambda([t], smt.If(c.val[t], x.val[t], y.val[t])))


def Implies(x: smt.DatatypeRef, y: smt.DatatypeRef) -> smt.DatatypeRef:
    """
    >>> x,y = smt.Consts("x y", TSort(smt.BoolSort()))
    >>> smt.simplify(Valid(Implies(x, y)))
    Or(Not(val(x)[0]), val(y)[0])
    """
    return lift_binop(x.sort(), smt.Implies)(x, y)


def Eq(x, y):
    """
    >>> x,y = smt.Consts("x y", TSort(smt.IntSort()))
    >>> smt.simplify(Valid(Eq(x,y)))
    val(x)[0] == val(y)[0]
    """
    t = smt.FreshInt("t")
    S = TSort(smt.BoolSort())
    return S(smt.Lambda([t], x.val[t] == y.val[t]))


def UNCHANGED(p):
    """
    >>> smt.simplify(Valid(UNCHANGED(TLift(1))))
    True
    """
    return Eq(Next(p), p)


def Valid(p: smt.DatatypeRef) -> smt.BoolRef:
    """
    The statement that the formula is true at `t = 0`.
    Convert a temporal formula into a Boolean.
    https://en.wikipedia.org/wiki/Kripke_semantics#Semantics_of_modal_logic

    """
    return p.val[0]


# Internal definitions for abstraction

p, q = smt.Consts("p q", TBool)
tnot = kd.define("tnot", [p], Not(p))
tand = kd.define("tand", [p, q], And(p, q))
tor = kd.define("tor", [p, q], Or(p, q))
timpl = kd.define("timpl", [p, q], Implies(p, q))
eventually = kd.define("eventually", [p], Eventually(p))
always = kd.define("always", [p], Always(p))
next = kd.define("next", [p], Next(p))

# annoyingly polymorphic
# tif = kd.define("tif", [p, q, r], If(p, q, r))
# teq
tiff = kd.define("tiff", [p, q], smt.Eq(p, q))
valid = kd.define("valid", [p], Valid(p))
