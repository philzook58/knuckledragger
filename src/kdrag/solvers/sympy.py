"""Export expressions for exploration with SymPy, without producing proofs.

SymPy's domains, branches, and treatment of undefined operations can differ from
Knuckledragger's. Legacy reverse translation helpers remain below for compatibility.
"""

import sys

import kdrag
import kdrag.smt as smt

import sympy

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


def sympy_const(e: smt.ExprRef) -> sympy.Expr:
    """
    >>> x = smt.FreshReal("x")
    >>> sympy_const(x)
    x!...
    """
    if not smt.is_const(e):
        raise ValueError(f"Expected a real or integer constant, got {e}")
    name = e.decl().name()
    if smt.is_real(e):
        return sympy.Symbol(name, real=True)
    if smt.is_int(e):
        return sympy.Symbol(name, integer=True)
    raise ValueError(f"Expected a real or integer constant, got {e}: {e.sort()}")


def sympify(e: smt.ExprRef, locals=None) -> sympy.Basic:
    """
    Export an expression to SymPy. Results are suggestions, not proofs.

    ``locals`` maps free constant or function names to SymPy objects. Bound
    variables are scoped independently. Calculus operators stay unevaluated;
    use native SymPy methods such as ``doit``, ``integrate``, and ``dsolve``.
    Sequence ``has_sum(a, L)`` becomes ``Eq(Sum(a(n), (n, 0, oo)), L)``.

    >>> x = smt.Real("x")
    >>> sympify(x + 1)
    x + 1
    >>> sympify(smt.RatVal(1,3))
    1/3
    >>> from kdrag.theories import real
    >>> sx = sympify(x)
    >>> sympy.integrate(sympify(x * real.exp(x)), sx)
    (x - 1)*exp(x)
    >>> y = smt.Const("y", real.RFun)
    >>> ode = sympify(real.deriv(y)[x] == y[x])
    >>> sympy.dsolve(ode, sympify(y[x]))
    Eq(y(x), C1*exp(x))
    """
    from kdrag.theories import real

    # Sequence expressions already require this theory; do not load its proofs
    # merely to export scalar arithmetic.
    seq = sys.modules.get("kdrag.theories.real.seq")
    if locals is None:
        locals = {}

    functions = {
        # Keep the legacy helpers' unprefixed declarations working too.
        sin: sympy.sin,
        cos: sympy.cos,
        tan: sympy.tan,
        asin: sympy.asin,
        acos: sympy.acos,
        exp: sympy.exp,
        ln: sympy.log,
        real.add: sympy.Add,
        real.sub: lambda x, y: x - y,
        real.mul: sympy.Mul,
        real.pow: sympy.Pow,
        real.sqr: lambda x: x**2,
        real.sqrt: sympy.sqrt,
        real.abs: sympy.Abs,
        real.sgn: sympy.sign,
        real.ln: sympy.log,
        real.exp: sympy.exp,
        real.sin: sympy.sin,
        real.cos: sympy.cos,
        real.tan: sympy.tan,
        real.asin: sympy.asin,
        real.acos: sympy.acos,
        real.atan: sympy.atan,
    }
    operators = {
        smt.Z3_OP_ADD: sympy.Add,
        smt.Z3_OP_SUB: lambda x, y: x - y,
        smt.Z3_OP_UMINUS: lambda x: -x,
        smt.Z3_OP_MUL: sympy.Mul,
        smt.Z3_OP_DIV: lambda x, y: x / y,
        smt.Z3_OP_POWER: sympy.Pow,
        smt.Z3_OP_TO_REAL: lambda x: x,
        smt.Z3_OP_EQ: lambda x, y: sympy.Eq(x, y, evaluate=False),
        smt.Z3_OP_LE: sympy.Le,
        smt.Z3_OP_LT: sympy.Lt,
        smt.Z3_OP_GE: sympy.Ge,
        smt.Z3_OP_GT: sympy.Gt,
        smt.Z3_OP_AND: sympy.And,
        smt.Z3_OP_OR: sympy.Or,
        smt.Z3_OP_NOT: sympy.Not,
        smt.Z3_OP_IMPLIES: sympy.Implies,
        smt.Z3_OP_ITE: lambda c, t, f: sympy.Piecewise((t, c), (f, True)),
        smt.Z3_OP_SELECT: lambda f, *xs: f(*xs),
    }

    def unsupported(t):
        raise ValueError(f"Cannot export to SymPy: {t} (sort {t.sort()})")

    def bound_symbol(name, sort):
        if sort == smt.RealSort():
            return sympy.Dummy(str(name), real=True)
        if sort == smt.IntSort():
            return sympy.Dummy(str(name), integer=True)
        return unsupported(smt.Const(str(name), sort))

    def worker(t, bound=()):
        if smt.is_var(t):
            index = smt.get_var_index(t)
            if index >= len(bound):
                return unsupported(t)
            return bound[index]
        if isinstance(t, smt.QuantifierRef):
            if not t.is_lambda():
                return unsupported(t)
            vs = [
                bound_symbol(t.var_name(i), t.var_sort(i)) for i in range(t.num_vars())
            ]
            return sympy.Lambda(
                tuple(vs), worker(t.body(), tuple(reversed(vs)) + bound)
            )
        if smt.is_int_value(t):
            return sympy.Integer(t.as_long())
        if smt.is_rational_value(t):
            return sympy.Rational(t.numerator_as_long(), t.denominator_as_long())
        if smt.is_true(t):
            return sympy.true
        if smt.is_false(t):
            return sympy.false
        if not smt.is_app(t):
            return unsupported(t)
        decl = t.decl()
        args = [worker(c, bound) for c in t.children()]
        if decl.kind() == smt.Z3_OP_UNINTERPRETED and decl.name() in locals:
            value = locals[decl.name()]
            return sympy.sympify(value(*args) if args else value)
        if decl in functions:
            return functions[decl](*args)
        if decl == real.pi.decl():
            return sympy.pi
        if smt.is_distinct(t) and len(args) == 2:
            return sympy.Ne(*args, evaluate=False)
        if decl.kind() in operators:
            return operators[decl.kind()](*args)
        if decl == real.ident.decl():
            x = sympy.Dummy("x", real=True)
            return sympy.Lambda(x, x)
        if decl == real.const:
            return sympy.Lambda(sympy.Dummy("x", real=True), args[0])
        if decl == real.has_lim_at:
            x = sympy.Dummy("x", real=True)
            limit = sympy.Limit(args[0](x), x, args[1], dir="+-")
            return sympy.Eq(limit, args[2], evaluate=False)
        if seq is not None and decl == seq.has_lim:
            n = sympy.Dummy("n", integer=True)
            limit = sympy.Limit(args[0](n), n, sympy.oo)
            return sympy.Eq(limit, args[1], evaluate=False)
        if seq is not None and decl == seq.has_sum:
            n = sympy.Dummy("n", integer=True)
            total = sympy.Sum(args[0](n), (n, 0, sympy.oo))
            return sympy.Eq(total, args[1], evaluate=False)
        if decl in (real.deriv, deriv, real.integrate, real.lim, real.summation):
            x = sympy.Dummy("x", real=True)
            body = args[0](x)
            if decl in (real.deriv, deriv):
                return sympy.Lambda(x, sympy.Derivative(body, x, evaluate=False))
            if decl == real.integrate:
                return sympy.Integral(body, (x, *args[1:]))
            if decl == real.lim:
                return sympy.Limit(body, x, args[1], dir="+-")
            return sympy.Sum(body, (x, *args[1:]))
        if smt.is_const_array(t) and t.sort() in (real.RFun, real.RSeq):
            return sympy.Lambda(bound_symbol("x", t.sort().domain()), args[0])
        if decl.kind() == smt.Z3_OP_UNINTERPRETED:
            if not args and (smt.is_real(t) or smt.is_int(t)):
                return sympy_const(t)
            if not args and t.sort() in (real.RFun, real.RSeq):
                x = bound_symbol("x", t.sort().domain())
                return sympy.Lambda(x, sympy.Function(decl.name(), real=True)(x))
            if decl.arity() == 1 and decl.domain(0) == R and decl.range() == R:
                return sympy.Function(decl.name(), real=True)(*args)
        return unsupported(t)

    return worker(e)


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
    if isinstance(e, sympy.Basic):
        svs = list(e.free_symbols)
    else:
        svs = []
    vs = [smt.Real(v.name) for v in svs if isinstance(v, sympy.Symbol)]
    return sympy.lambdify(
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
    return kdify(sympy.factor(sympify(e)))


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
    return kdify(sympy.diff(sympify(e), *translate_tuple_args(args)))


def integrate(e, *args):
    """
    Integrate a z3 expression.
    >>> x = smt.Real("x")
    >>> integrate(x**2, x)
    x**3*1/3
    """
    return kdify(sympy.integrate(sympify(e), translate_tuple_args(args)))


def summation(e, *args):
    """
    Sum a z3 expression.
    >>> x,n = smt.Reals("x n")
    >>> summation(x**2, (x, 0, 10))
    385
    >>> summation(x, (x, 0, n))
    n**2*1/2 + n*1/2
    """
    return kdify(sympy.summation(sympify(e), *translate_tuple_args(args)))


def series(e, x=None, x0=0, n=6, dir="+"):
    """
    Compute the series expansion of a z3 expression.
    >>> x = smt.Real("x")
    >>> series(sin(x), x, n=2)
    x + Order(x**2)
    """
    if x is not None:
        x = sympify(x)
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
    x = sympify(x)
    return kdify(sympy.limit(sympify(e), x, x0))


def solve(
    constrs: list[smt.BoolRef], vs: list[smt.ExprRef]
) -> list[dict[smt.ExprRef, smt.ExprRef]]:
    """

    >>> x,y,z = smt.Reals("x y z")
    >>> solve([x + y == 1, x - z == 2], [x, y, z])
    [{x: z + 2, y: -z - 1}]
    >>> solve([cos(x) == 3], [x])  # No real solutions.
    []
    """
    assert isinstance(vs, list) and isinstance(constrs, list)
    sols = sympy.solve(
        [sympify(constr) for constr in constrs], [sympify(v) for v in vs], dict=True
    )
    return [{kdify(v): kdify(t) for v, t in sol.items()} for sol in sols]
