import kdrag.theories.real as real
import kdrag as kd
import kdrag.reflect
import kdrag.smt as smt
import flint
import operator as op
import sympy
import sympy.abc

arb = flint.arb  # type: ignore
a, b = smt.Reals("a b")
flint_decls = {
    real.sqrt: arb.sqrt,
    real.sqr: lambda x: x**2,
    real.exp: arb.exp,
    real.ln: arb.log,
    real.sin: arb.sin,
    real.cos: arb.cos,
    real.tan: arb.tan,
    real.atan: arb.atan,
    real.pow: lambda x, y: x**y,
    real.pi.decl(): arb.pi,
    (a + b).decl(): op.add,
    (a * b).decl(): op.mul,
    (a / b).decl(): op.truediv,
    (a - b).decl(): op.sub,
    (a**b).decl(): op.pow,
}


def interp_flint(e, env):
    if e in env:
        return env[e]
    elif smt.is_select(e) and e.arg(0) in flint_decls:
        return flint_decls[e.arg(0)](
            *[interp_flint(arg, env) for arg in e.children()[1:]]
        )
    elif smt.is_rational_value(e):
        return arb(e.numerator_as_long()) / arb(e.denominator_as_long())
    elif smt.is_app(e) and e.decl() in flint_decls:
        decl = e.decl()
        return flint_decls[decl](*[interp_flint(arg, env) for arg in e.children()])
    assert False, f"Can't interpret {e} into flint"


def z3_of_arb(x: flint.arb) -> tuple[smt.ArithRef, smt.ArithRef]:  # type: ignore
    if not x.is_finite():
        raise ValueError("Infinite value in z3_of_arb", x)
    mid = x.mid().str(100, more=True, radius=True)
    rad = x.rad().str(100, more=True, radius=True)
    # +/- does not appear if matches arb exactly
    if "+/-" in mid or "+/-" in rad:
        raise ValueError("Unexpected error in conversion from arb to z3", mid, rad)
    return smt.RealVal(mid), smt.RealVal(rad)


def flint_bnd(t: smt.ExprRef, env):
    assert smt.is_real(t)
    assert all(smt.is_real(k) and isinstance(v, arb) for k, v in env.items())
    preconds = [smt.BoolVal(True)]
    for k, v in env.items():
        mid, rad = z3_of_arb(v)
        preconds.append(mid - rad <= k)
        preconds.append(k <= mid + rad)
    v = interp_flint(t, env)
    if not v.is_finite():
        raise ValueError("Infinite value in flint_bnd", t, env, v)
    mid, rad = z3_of_arb(v)
    if len(env) > 0:
        return kd.axiom(
            kd.QForAll(
                list(env.keys()), smt.And(preconds), mid - rad <= t, t <= mid + rad
            ),
            by="flint_eval",
        )
    else:
        return kd.axiom(smt.And(mid - rad <= t, t <= mid + rad), by="flint_eval")


"""
a, b = smt.Reals("a b")
sympy_decls = {
    real.sqrt: sympy.sqrt,
    real.sqr: lambda x: x**2,
    real.exp: sympy.exp,
    real.ln: sympy.ln,
    real.sin: sympy.sin,
    real.cos: sympy.cos,
    real.tan: sympy.tan,
    real.atan: sympy.atan,
    real.pi.decl(): sympy.pi,
    (a + b).decl(): sympy.Add,
    (a * b).decl(): sympy.Mul,
    (a / b).decl(): op.truediv,
    (a - b).decl(): op.sub,
    (a**b).decl(): sympy.Pow,
    (a == b).decl(): sympy.Eq,
}
sympy_consts = {
    real.pi: sympy.pi,
}
rev_sympy_decls = {v: k for k, v in sympy_decls.items()}
rev_sympy_consts = {v: k for k, v in sympy_consts.items()}


def interp_sympy(e: smt.ExprRef, env: dict[smt.ExprRef, sympy.Expr] = {}) -> sympy.Expr:
    if e in env:
        return env[e]
    elif e in sympy_consts:
        return sympy_consts[e]
    elif smt.is_rational_value(e) and isinstance(e, smt.RatNumRef):
        return sympy.Rational(e.numerator_as_long(), e.denominator_as_long())
    elif smt.is_select(e) and e.arg(0) in sympy_decls:
        return sympy_decls[e.arg(0)](
            *[interp_sympy(arg, env) for arg in e.children()[1:]]
        )
    elif smt.is_app(e) and e.decl() in sympy_decls:
        decl = e.decl()
        return sympy_decls[decl](*[interp_sympy(arg, env) for arg in e.children()])
    else:
        raise ValueError(f"Can't interpret {e} into sympy")


def z3_of_sympy(x: sympy.Basic, env: dict[sympy.Expr, smt.ExprRef] = {}) -> smt.ExprRef:
    if x in env:
        return env[x]
    elif x in rev_sympy_consts:
        return rev_sympy_consts[x]
    elif x.is_constant() and x.is_rational:  # type: ignore
        num, denom = x.as_numer_denom()  # type: ignore
        return smt.RatVal(int(num), int(denom))
    elif x.func in rev_sympy_decls:
        decl = rev_sympy_decls[x.func]
        return decl(*[z3_of_sympy(arg, env) for arg in x.args])
    else:
        raise ValueError("Can't interpret", x, "from sympy into z3")


def wrap_sympy(f):
    def wrapped(vs, e: smt.ExprRef, **kwargs):
        env1 = {e: sympy.symbols(e.decl().name()) for e in vs}
        env2 = {v: k for k, v in env1.items()}
        e_sym = interp_sympy(e, env1)
        t = z3_of_sympy(f(e_sym, **kwargs), env2)
        return t

    return wrapped



factor = wrap_sympy(sympy.factor)
expand = wrap_sympy(sympy.expand)
simplify = wrap_sympy(sympy.simplify)
expand_trig = wrap_sympy(sympy.expand_trig)
collect = wrap_sympy(sympy.collect)
"""

sympy_env = {**sympy.__dict__, **sympy.abc.__dict__}


def sympify(e: smt.ExprRef, locals={}) -> sympy.Expr:  # type: ignore
    """
    Convert a z3 expression into a sympy expression.
    >>> x = smt.Real("x")
    >>> sympify(x + 1)
    x + 1
    >>> sympify(smt.RatVal(1,3))
    Fraction(1, 3)
    """
    return kdrag.reflect.eval_(e, sympy_env, locals={})


def replace_rational_with_ratval(expr):
    """
    Replace all Rational numbers in a SymPy expression with z3.RatVal equivalents.

    >>> x = smt.Real("x")
    >>> replace_rational_with_ratval(sympify(x + smt.RatVal(1,3)))
    x + RatVal(1, 3)
    """
    if isinstance(expr, sympy.Rational):
        if expr.q == 1:
            return expr
        # elif (float(expr) - expr).is_zero: # Doesn't seem to work
        #    return expr
        else:
            return sympy.Function("RatVal")(expr.p, expr.q)  # type: ignore
    elif isinstance(expr, sympy.Order):
        return sympy.Function("Order")(expr.expr)  # , expr.point) # type: ignore
    elif expr.is_Atom:
        return expr
    else:
        args = [replace_rational_with_ratval(arg) for arg in expr.args]
        return expr.func(*args, evaluate=False)


def kdify(e: sympy.Expr, **kwargs) -> smt.ExprRef:
    """
    Convert a sympy expression into a z3 expression.
    >>> x = smt.Real("x")
    >>> kdify(sympify(x + 1))
    x + 1
    >>> kdify(sympify(real.sin(x) + 1))
    sin(x) + 1
    >>> kdify(sympify(x + smt.RatVal(1,3)))
    x + 1/3
    >>> kdify(sympify(x/3))
    x*1/3
    """
    if isinstance(e, sympy.Basic):  # type: ignore
        svs = list(e.free_symbols)
    else:
        svs = []
    vs = [smt.Real(v.name) for v in svs]  # type: ignore
    return sympy.lambdify(  # type: ignore
        svs,
        replace_rational_with_ratval(e),
        modules=[
            {
                "RatVal": smt.RatVal,
                "Order": smt.Function("Order", smt.RealSort(), smt.RealSort()),
            },
            real,
        ],
        **kwargs,
    )(*vs)


def expand(e: smt.ExprRef) -> smt.ExprRef:
    """
    Expand a z3 expression.
    >>> x = smt.Real("x")
    >>> expand((x + 1)**2)
    x**2 + 2*x + 1
    """
    return kdify(sympy.expand(sympify(e)))


def factor(e: smt.ExprRef) -> smt.ExprRef:
    """
    Factor a z3 expression.
    >>> x = smt.Real("x")
    >>> factor(x**2 + 2*x + 1)
    (x + 1)**2
    """
    return kdify(sympy.factor(sympify(e)))  # type: ignore


def simplify(e: smt.ExprRef) -> smt.ExprRef:
    """
    Simplify a z3 expression.
    >>> x = smt.Real("x")
    >>> simplify((x + 1)**2 - x**2)
    2*x + 1
    >>> simplify(real.sin(x)**2 + real.cos(x)**2)
    1
    """
    return kdify(sympy.simplify(sympify(e)))


def translate_tuple_args(args):
    res = []
    for arg in args:
        if isinstance(arg, int) or isinstance(arg, str) or isinstance(arg, float):
            res.append(arg)
        if isinstance(arg, smt.ExprRef):
            res.append(sympify(arg))
        elif isinstance(arg, tuple):
            res.append(translate_tuple_args(arg))
    return tuple(res)


def diff(e: smt.ExprRef, *args):
    """
    Differentiate a z3 expression.
    >>> x,y = smt.Reals("x y")
    >>> diff(x**2, x)
    2*x
    >>> diff(x**2, x, x)
    2
    >>> diff(x*x, (x,2))
    2
    >>> diff(x*y*x, x)
    2*x*y
    """
    return kdify(sympy.diff(sympify(e), *translate_tuple_args(args)))  # type: ignore


def integrate(e, *args):
    """
    Integrate a z3 expression.
    >>> x = smt.Real("x")
    >>> integrate(x**2, x)
    x**3*1/3
    """
    return kdify(sympy.integrate(sympify(e), translate_tuple_args(args)))  # type: ignore


def summation(e, *args):
    """
    Sum a z3 expression.
    >>> x,n = smt.Reals("x n")
    >>> summation(x**2, (x, 0, 10))
    385
    >>> summation(x, (x, 0, n))
    n**2*1/2 + n*1/2
    """
    return kdify(sympy.summation(sympify(e), *translate_tuple_args(args)))  # type: ignore


def series(e, x=None, x0=0, n=6, dir="+"):
    """
    Compute the series expansion of a z3 expression.
    >>> x = smt.Real("x")
    >>> series(real.sin(x), x, n=2)
    x + Order(x**2)
    """
    if x is not None:
        x = sympy.symbols(x.decl().name())  # type: ignore
    return kdify(sympy.series(sympify(e), x, x0, n, dir))


def limit(e, x, x0):
    """
    Compute the limit of a z3 expression.
    >>> x = smt.Real("x")
    >>> limit(1/x, x, sympy.oo)
    0
    >>> limit(1/x, x, 0) # TODO: What to do about this one?
    inf
    """
    x = sympy.symbols(x.decl().name())  # type: ignore
    return kdify(sympy.limit(sympify(e), x, x0))
