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
        t = smt.FreshInt("t")
        return S(smt.Lambda([t], op(x.val[t], y1.val[t])))

    return res


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
    return S

    # kd.notation.eq.register(S, lift(operator.eq))


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
    assert all(x.sort() == TSort(smt.BoolSort()) for x in args)
    if len(args) == 0:
        return TLift(smt.BoolVal(True))
    elif len(args) == 1:
        return args[0]
    return functools.reduce(operator.and_, args)


def Or(*args):
    """

    >>> _ = Or(TLift(True), TLift(False))
    """
    assert all(x.sort() == TSort(smt.BoolSort()) for x in args)
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


def Always(x):
    assert x.sort() == TSort(smt.BoolSort())
    t = smt.FreshInt("t")
    dt = smt.FreshInt("dt")
    S = x.sort()
    return S(smt.Lambda([t], kd.QForAll([dt], dt >= 0, x.val[t + dt])))


def If(c: smt.DatatypeRef, x: smt.DatatypeRef, y: smt.DatatypeRef) -> smt.DatatypeRef:
    """
    >>> _ = If(TLift(True), TLift(1), TLift(2))
    """
    t = smt.FreshInt("t")
    assert x.sort() == y.sort()
    assert c.sort() == TSort(smt.BoolSort())
    S = x.sort()
    return S(smt.Lambda([t], smt.If(c.val[t], x.val[t], y.val[t])))


def Implies(x: smt.DatatypeRef, y: smt.DatatypeRef) -> smt.DatatypeRef:
    """
    >>> x,y = smt.Consts("x y", TSort(smt.BoolSort()))
    >>> smt.simplify(Eval0(Implies(x, y)))
    Or(Not(val(x)[0]), val(y)[0])
    """
    return lift_binop(x.sort(), smt.Implies)(x, y)


def Eq(x, y):
    """
    >>> x,y = smt.Consts("x y", TSort(smt.IntSort()))
    >>> smt.simplify(Eval0(Eq(x,y)))
    val(x)[0] == val(y)[0]
    """
    t = smt.FreshInt("t")
    S = TSort(smt.BoolSort())
    return S(smt.Lambda([t], x.val[t] == y.val[t]))


def UNCHANGED(p):
    """
    >>> smt.simplify(Eval0(UNCHANGED(TLift(1))))
    True
    """
    return Eq(Next(p), p)


def Eval0(p: smt.DatatypeRef) -> smt.BoolRef:
    """ """
    return p.val[0]
