# import kdrag.theories.real as real
import kdrag.reflect
import kdrag.smt as smt

import sympy
import sympy.abc

R = smt.RealSort()
RFun = smt.ArraySort(R, R)
cos = smt.Function("cos", smt.RealSort(), smt.RealSort())
sin = smt.Function("sin", smt.RealSort(), smt.RealSort())
tan = smt.Function("tan", smt.RealSort(), smt.RealSort())
acos = smt.Function("acos", smt.RealSort(), smt.RealSort())
asin = smt.Function("asin", smt.RealSort(), smt.RealSort())
deriv = smt.Function(
    "deriv", smt.ArraySort(smt.RealSort(), smt.RealSort()), smt.RealSort()
)
exp = smt.Function("exp", smt.RealSort(), smt.RealSort())
integrate_ = smt.Function("integrate", smt.ArraySort(R, R), R, R, R)
summation_ = smt.Function("summation", smt.ArraySort(R, R), R, R, R)
lim = smt.Function("lim", RFun, R, R)
pi = smt.Const("pi", R)
ln = smt.Function("ln", R, R)


def shim_ho(f):
    def res(e: kdrag.reflect.KnuckleClosure):
        x = sympy.symbols("x", real=True)
        return f(e(x), x)  # wrong

    return res


def fresh_symbol() -> sympy.Symbol:
    """
    Create a fresh symbol for use in sympy expressions.
    >>> x = fresh_symbol()
    >>> y = fresh_symbol()
    >>> x != y
    True
    """
    return sympy.Symbol(
        smt.FreshConst(smt.RealSort()).decl().name().replace("!", "__"), real=True
    )


def diff_shim(e: kdrag.reflect.KnuckleClosure) -> sympy.Basic:
    assert e.lam.num_vars() == 1 and e.lam.var_sort(0) == smt.RealSort()
    x = fresh_symbol()
    e.locals[x.name] = x
    return sympy.Lambda(x, sympy.diff(e(x), x, evaluate=False))


def integ_shim(e: kdrag.reflect.KnuckleClosure, a, b) -> sympy.Basic:
    assert e.lam.num_vars() == 1 and e.lam.var_sort(0) == smt.RealSort()
    x = fresh_symbol()
    e.locals[x.name] = x
    return sympy.integrate(e(x), (x, a, b))


def sum_shim(e: kdrag.reflect.KnuckleClosure, a, b) -> sympy.Basic:
    assert e.lam.num_vars() == 1 and e.lam.var_sort(0) == smt.RealSort()
    x = fresh_symbol()
    e.locals[x.name] = x
    return sympy.summation(e(x), (x, a, b))  # type: ignore


sympy_env = {
    **sympy.__dict__,
    **sympy.abc.__dict__,
    "=": sympy.Eq,
    "exp": lambda x: sympy.E**x,
    "deriv": diff_shim,
    "integrate": integ_shim,
    "summation": sum_shim,
}


def sympify(e: smt.ExprRef, locals=None) -> sympy.Expr:  # type: ignore
    """
    Convert a z3 expression into a sympy expression.
    >>> x = smt.Real("x")
    >>> sympify(x + 1)
    x + 1
    >>> sympify(smt.RatVal(1,3))
    Fraction(1, 3)
    >>> sympify(deriv(smt.Lambda([x], cos(sin(x)))))(sympy.abc.x)
    Derivative(cos(sin(x)), x)
    >>> sympify(integrate_(smt.Lambda([x], sin(x)), 0,x))
    1 - cos(x)
    >>> sympify(smt.Lambda([x], x + 1))
    Lambda(X__..., X__... + 1)
    """
    if locals is None:
        locals = {}
    res = kdrag.reflect.eval_(e, globals=sympy_env, locals=locals)
    if isinstance(res, kdrag.reflect.KnuckleClosure):
        vs, body = kdrag.utils.open_binder(res.lam)
        vs1 = []
        for v in vs:
            v1 = sympy.Symbol(v.decl().name().replace("!", "__"), real=True)
            vs1.append(v1)
            locals[v.decl().name()] = v1
        return sympy.Lambda(
            tuple(vs1),
            sympify(body, locals=locals),
        )
    else:
        return res


def _sympy_mangle(expr: sympy.Basic) -> sympy.Basic:
    """
    Replace all Rational numbers in a SymPy expression with z3.RatVal equivalents.

    >>> x = smt.Real("x")
    >>> _sympy_mangle(sympify(x + smt.RatVal(1,3)))
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
    elif expr == sympy.E:  # Sympy turns Euler constant into fraction otherwise
        return sympy.Symbol("e")
    elif isinstance(expr, sympy.Lambda):
        # KD Lambda is a hack to avoid lambdify issues. We break lambda abstraction. Probably this goes horribly wrong
        f = sympy.Function("KD_Lambda")
        return f(expr.variables, _sympy_mangle(expr.expr))  # type: ignore
    elif expr.is_Atom:
        return expr
    else:
        args = [_sympy_mangle(arg) for arg in expr.args]
        return expr.func(*args)


def kdify(e: sympy.Basic, **kwargs) -> smt.ExprRef:
    """
    Convert a sympy expression into a z3 expression.
    >>> x = smt.Real("x")
    >>> kdify(sympify(x + 1))
    x + 1
    >>> kdify(sympify(sin(x) + 1))
    sin(x) + 1
    >>> kdify(sympify(x + smt.RatVal(1,3)))
    x + 1/3
    >>> kdify(sympify(x/3))
    x*1/3
    """
    e = _sympy_mangle(e)
    if isinstance(e, sympy.Basic):  # type: ignore
        svs = list(e.free_symbols)
    else:
        svs = []
    vs = [smt.Real(v.name) for v in svs]  # type: ignore
    return sympy.lambdify(  # type: ignore
        svs,
        e,
        modules=[
            {
                "RatVal": smt.RatVal,
                "Order": smt.Function("Order", smt.RealSort(), smt.RealSort()),
                # "Lambda": lambda x, y: smt.Lambda(kdify(x), kdify(y)),
                "KD_Lambda": smt.Lambda,
                "sin": sin,
                "cos": cos,
                "tan": tan,
                "acos": acos,
                "asin": asin,
                "exp": exp,
                "ln": ln,
                "integrate": integrate,
                "pi": pi,
            },
            # real,
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
    >>> simplify(sin(x)**2 + cos(x)**2)
    1
    """
    return kdify(sympy.simplify(sympify(e)))


def simp(e: smt.ExprRef) -> kdrag.kernel.Proof:
    """
    Sympy simplification as an axiom schema.
    Sympy nor the translation to and from z3 are particularly sound.
    It is very useful though and better than nothing.
    Your mileage may vary

    >>> x = smt.Real("x")
    >>> simp(sin(x)**2 + cos(x)**2)
    |= sin(x)**2 + cos(x)**2 == 1
    """
    return kdrag.kernel.axiom(e == simplify(e), by=["sympy simplify"])  # type: ignore


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
    >>> series(sin(x), x, n=2)
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


def solve(
    constrs: list[smt.BoolRef], vs: list[smt.ExprRef]
) -> list[dict[smt.ExprRef, smt.ExprRef]]:
    """

    >>> x,y,z = smt.Reals("x y z")
    >>> solve([x + y == 1, x - z == 2], [x, y, z])
    [{x: z + 2, y: -z - 1}]
    >>> solve([cos(x) == 3], [x]) # Note that does not return all possible solutions.
    [{x: 2*pi - acos(3)}, {x: acos(3)}]
    """
    assert isinstance(vs, list) and isinstance(constrs, list)
    sols = sympy.solve(
        [sympify(constr) for constr in constrs], [sympify(v) for v in vs], dict=True
    )
    return [{kdify(v): kdify(t) for v, t in sol.items()} for sol in sols]


"""
# Old Style. Remove?

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
