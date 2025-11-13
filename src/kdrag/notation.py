"""
SortDispatch system for z3 sort based dispatch akin to `functools.singledispatch`.

The `SortDispatch` system enables z3 sort based dispatch akin to ` functools.singledispatch`.
This is the mechanism for operator overloading in knuckledragger.

A special overloadable operation is the "well-formed" predicate `wf`.
Using the QForAll and QExists quantifiers will automatically insert `wf` calls for the appropriate sorts.
In this way, we can achieve an effect similar to refinement types.

Importing this module will add some syntactic sugar to smt.

- Expr overload by single dispatch
- Bool supports `&`, `|`, `~`
- Sorts supports `>>` for ArraySort
"""

import kdrag.smt as smt
import kdrag as kd


smt.SortRef.__rshift__ = lambda self, other: smt.ArraySort(self, other)  # type: ignore

smt.ArrayRef.__call__ = lambda self, *arg: self[arg]


def quantifier_call(self, *args):
    """
    Instantiate a quantifier. This does substitution
    >>> x,y = smt.Ints("x y")
    >>> smt.Lambda([x,y], x + 1)(2,3)
    2 + 1

    To apply a Lambda without substituting, use square brackets
    >>> smt.Lambda([x,y], x + 1)[2,3]
    Select(Lambda([x, y], x + 1), 2, 3)
    """
    if self.num_vars() != len(args):
        raise TypeError("Wrong number of arguments", self, args)
    return smt.substitute_vars(
        self.body(), *(smt._py2expr(arg) for arg in reversed(args))
    )


smt.QuantifierRef.__call__ = quantifier_call


class SortDispatch:
    """
    Sort dispatch is modeled after functools.singledispatch
    It allows for dispatching on the sort of the first argument

    >>> my_func = SortDispatch(name="my_func")
    >>> my_func.register(smt.IntSort(), lambda x: x + 1)
    >>> my_func.register(smt.BoolSort(), lambda x: smt.Not(x))
    >>> my_func(smt.IntVal(3))
    3 + 1
    >>> my_func(smt.BoolVal(True))
    Not(True)
    """

    def __init__(self, name=None, default=None, pointwise=False, default_factory=None):
        self.methods = {}
        self.default = default
        self.name = name
        self.pointwise = pointwise
        self.default_factory = default_factory

    def register(self, sort, func):
        self.methods[sort] = func

    def __getitem__(self, sort):
        return self.methods[sort]

    def __contains__(self, sort):
        return sort in self.methods

    def __call__(self, *args, **kwargs):
        """

        TODO: Overloading in theories.set is interfering. Which to keep?
        # >>> _ = smt.Lambda([x], x > 0) & smt.BoolVal(False)

        >>> x = smt.Int("x")
        >>> _ = smt.Lambda([x], x > 0) & smt.Lambda([x], x > 1)
        >>> foo = SortDispatch("foo", pointwise=True)
        >>> foo.register(smt.IntSort(), lambda x: x + 1)
        >>> foo(x)
        x + 1
        >>> z = smt.Array("z", smt.RealSort(), smt.IntSort())
        >>> foo(z)
        Lambda(x0!..., z[x0!...] + 1)
        >>> smt.Lambda([x], x) + smt.Lambda([x], x)
        Lambda(x0!..., x0!... + x0!...)
        >>> smt.Lambda([x], x) + 1
        Lambda(x0!..., x0!... + 1)
        """
        if not args:
            raise TypeError("No arguments provided")
        x0 = args[0]
        sort = args[0].sort()
        res = self.methods.get(sort)
        if res is not None:
            return res(*args, **kwargs)
        elif self.default is not None:
            return self.default(*args, **kwargs)
        elif self.default_factory is not None:
            res = self.default_factory(sort)
            self.register(sort, res)
            return res(*args, **kwargs)
        elif self.pointwise and smt.is_func(x0):
            doms = smt.domains(x0)
            vs = [smt.FreshConst(d, prefix=f"x{n}") for n, d in enumerate(doms)]
            # sorts are same or attempt coerce/lift
            return smt.Lambda(
                vs,
                self(
                    *[
                        arg(*vs)
                        if isinstance(arg, smt.ExprRef) and arg.sort() == x0.sort()
                        else arg
                        for arg in args
                    ]
                ),
            )
        else:
            raise NotImplementedError(
                f"No implementation of {self.name} for sort {sort}. Register a definition via {self.name}.register({sort}, your_code)",
            )
        return res(*args, **kwargs)

    def define(self, args, body):
        """
        Shorthand to define a new function for this dispatch. Calls kdrag.define.
        """
        assert isinstance(self.name, str)
        defn = kd.define(self.name, args, body)
        self.register(args[0].sort(), defn)
        return defn


def GenericDispatch(default_factory) -> SortDispatch:
    """
    A decorator version of SortDispatch with a default factory.
    This is useful for definition Sort generic definitions.

    >>> @GenericDispatch
    ... def id(sort):
    ...    x = smt.Const("x", sort)
    ...    return kd.define("id", [x], x)
    >>> id(smt.IntVal(3))
    id(3)
    """
    return SortDispatch(default_factory.__name__, default_factory=default_factory)


call = SortDispatch(name="call")
"""Sort based dispatch for `()` call syntax"""
smt.ExprRef.__call__ = lambda x, *y, **kwargs: call(x, *y, **kwargs)  # type: ignore

getitem = SortDispatch(name="getitem")
"""Sort based dispatch for `[]` getitem syntax"""
smt.ExprRef.__getitem__ = lambda x, y: getitem(x, y)  # type: ignore


add = SortDispatch(name="add", pointwise=True)
"""Sort based dispatch for `+` syntax"""
smt.ExprRef.__add__ = lambda x, y: add(x, y)  # type: ignore
# BoolRef has an __add__ method, and QuantifierRef subclasses it even though this makes no sense.
# Clearing this restores better behavior.
smt.QuantifierRef.__add__ = lambda x, y: add(x, y)  # type: ignore

_n, _m = smt.Ints("n m")
_x, _y = smt.Reals("x y")
add.register(smt.IntSort(), (_n + _m).decl())
add.register(smt.RealSort(), (_x + _y).decl())


radd = SortDispatch(name="radd", pointwise=True)
"""Sort based dispatch for `+` syntax"""
radd.register(smt.IntSort(), (_n + _m).decl())
radd.register(smt.RealSort(), (_x + _y).decl())
smt.ExprRef.__radd__ = lambda x, y: radd(x, y)  # type: ignore


sub = SortDispatch(name="sub", pointwise=True)
"""Sort based dispatch for `-` syntax"""
sub.register(smt.IntSort(), lambda x, y: x - y)
sub.register(smt.RealSort(), lambda x, y: x - y)
smt.ExprRef.__sub__ = lambda x, y: sub(x, y)  # type: ignore
smt.QuantifierRef.__sub__ = lambda x, y: sub(x, y)  # type: ignore

mul = SortDispatch(name="mul", pointwise=True)
"""Sort based dispatch for `*` syntax"""
mul.register(smt.IntSort(), lambda x, y: x * y)
mul.register(smt.RealSort(), lambda x, y: x * y)
smt.ExprRef.__mul__ = lambda x, y: mul(x, y)  # type: ignore
smt.QuantifierRef.__mul__ = lambda x, y: mul(x, y)  # type: ignore

rmul = SortDispatch(name="rmul", pointwise=True)
"""Sort based dispatch for `*` syntax"""
smt.ExprRef.__rmul__ = lambda x, y: rmul(x, y)  # type: ignore


matmul = SortDispatch(name="matmul", pointwise=True)
"""Sort based dispatch for `@` syntax"""
smt.ExprRef.__matmul__ = lambda x, y: matmul(x, y)  # type: ignore

neg = SortDispatch(name="neg", pointwise=True)
"""Sort based dispatch for `-` syntax"""
neg.register(smt.IntSort(), lambda x: -x)
neg.register(smt.RealSort(), lambda x: -x)
smt.ExprRef.__neg__ = lambda x: neg(x)  # type: ignore

div = SortDispatch(name="div_", pointwise=True)
"""Sort based dispatch for `/` syntax"""
smt.ExprRef.__truediv__ = lambda x, y: div(x, y)  # type: ignore

and_ = SortDispatch(name="and_", pointwise=True)
"""Sort based dispatch for `&` syntax"""
smt.ExprRef.__and__ = lambda x, y: and_(x, y)  # type: ignore
smt.QuantifierRef.__and__ = lambda x, y: and_(x, y)  # type: ignore
and_.register(smt.BoolSort(), smt.And)

or_ = SortDispatch(name="or_", pointwise=True)
"""Sort based dispatch for `|` syntax"""
smt.ExprRef.__or__ = lambda x, y: or_(x, y)  # type: ignore
smt.QuantifierRef.__or__ = lambda x, y: or_(x, y)  # type: ignore
or_.register(smt.BoolSort(), smt.Or)

invert = SortDispatch(name="invert", pointwise=True)
"""Sort based dispatch for `~` syntax"""
smt.ExprRef.__invert__ = lambda x: invert(x)  # type: ignore
smt.QuantifierRef.__invert__ = lambda x: invert(x)  # type: ignore
invert.register(smt.BoolSort(), smt.Not)

lt = SortDispatch(name="lt", pointwise=True)
"""Sort based dispatch for `<` syntax"""
smt.ExprRef.__lt__ = lambda x, y: lt(x, y)  # type: ignore
lt.register(smt.IntSort(), lambda x, y: x < y)
lt.register(smt.RealSort(), lambda x, y: x < y)
# Conceptually this kind of makes sense, but SubSet is the more natural thing.
# lt.register(smt.BoolSort(), lambda x, y: smt.And(smt.Not(x), y))


le = SortDispatch(name="le", pointwise=True)
"""Sort based dispatch for `<=` syntax"""
smt.ExprRef.__le__ = lambda x, y: le(x, y)  # type: ignore
le.register(smt.IntSort(), lambda x, y: x <= y)
le.register(smt.RealSort(), lambda x, y: x <= y)
# le.register(smt.BoolSort(), lambda x, y: smt.Implies(x, y))

ge = SortDispatch(name="ge", pointwise=True)
"""Sort based dispatch for `>=` syntax"""
smt.ExprRef.__ge__ = lambda x, y: ge(x, y)  # type: ignore
ge.register(smt.IntSort(), lambda x, y: x >= y)
ge.register(smt.RealSort(), lambda x, y: x >= y)
# ge.register(smt.BoolSort(), lambda x, y: smt.Implies(y, x))

gt = SortDispatch(name="gt", pointwise=True)
"""Sort based dispatch for `>` syntax"""
smt.ExprRef.__gt__ = lambda x, y: gt(x, y)  # type: ignore
gt.register(smt.IntSort(), lambda x, y: x > y)
gt.register(smt.RealSort(), lambda x, y: x > y)
# gt.register(smt.BoolSort(), lambda x, y: smt.And(x, smt.Not(y)))

# contains cannot work because python demands a concrete bool.
# contains = SortDispatch(name="contains")
# smt.ExprRef.__contains__ = lambda x, y: contains(x, y)  # type: ignore

eq = SortDispatch(name="eq", default=smt.Eq)
"""Sort based dispatch for `==` syntax"""
smt.ExprRef.__eq__ = lambda x, y: eq(x, y)  # type: ignore


ne = SortDispatch(name="ne", default=smt.NEq)
"""Sort based dispatch for `!=` syntax"""
smt.ExprRef.__ne__ = lambda x, y: ne(x, y)  # type: ignore

wf = SortDispatch(name="wf")
"""`wf` is a special predicate for well-formedness. It is auto inserted by QForAll and QExists."""
smt.ExprRef.wf = lambda x: wf(x)  # type: ignore

measure = SortDispatch(name="measure")
"""`measure is an Int value associated with an ExprRef for use in defining well-founded recursion."""
# smt.ExprRef.measure = lambda x: measure(x)  # type: ignore
measure.register(smt.IntSort(), lambda x: smt.Abs(x))  # type: ignore
measure.register(smt.BoolSort(), lambda x: smt.If(x, smt.IntVal(1), smt.IntVal(0)))

choose = SortDispatch(name="choose")
"""Sort based dispatch for Hilbert choice operator."""
# smt.ExprRef.choose = lambda P: choose(P)  # type: ignore

# These are of questionable utility, but conceptually should be here.
forall = SortDispatch(name="forall")
"""Sort based dispatch for `ForAll` quantifier."""
# smt.ExprRef.forall = lambda vs, body: forall(vs, body)

exists = SortDispatch(name="exists")
"""Sort based dispatch for `Exists` quantifier."""
# smt.ExprRef.exists = lambda vs, body: exists(vs, body)


def induct_seq(a: smt.SeqRef, P) -> kd.kernel.Proof:
    """
    >>> x = smt.Const("x", smt.SeqSort(smt.IntSort()))
    >>> induct(x, lambda s: smt.Length(s) >= 0)
    |= Implies(And(Length(Empty(Seq(Int))) >= 0,
                ForAll(z!..., Length(Unit(z!...)) >= 0),
                ForAll([x!..., y!...],
                       Implies(And(Length(x!...) >= 0,
                                   Length(y!...) >= 0),
                               Length(Concat(x!..., y!...)) >= 0))),
            Length(x) >= 0)
    """
    assert isinstance(a, smt.SeqRef)
    sort = a.sort()
    T = sort.basis()
    z = smt.FreshConst(T, prefix="z")
    x, y = smt.FreshConst(sort, prefix="x"), smt.FreshConst(sort, prefix="y")
    return kd.axiom(
        smt.Implies(
            smt.And(
                P(smt.Empty(sort)),
                QForAll([z], P(smt.Unit(z))),
                QForAll([x, y], P(x), P(y), P(smt.Concat(x, y))),
            ),
            # -------------------------------------------------
            P(a),
        )
    )


def induct_default(x, P):
    if isinstance(x, smt.SeqRef):
        return induct_seq(x, P)
    else:
        raise NotImplementedError("No default induct implementation for sort", x.sort())


induct = SortDispatch(name="induct", default=induct_default)
"""Sort based dispatch for induction principles. Should instantiate an induction scheme for variable x and predicate P"""
smt.ExprRef.induct = lambda x, P: induct(x, P)  # type: ignore


def induct_int(x, P):
    n = smt.FreshConst(smt.IntSort(), prefix="n")
    # P = smt.FreshConst(smt.ArraySort(Z, smt.BoolSort()), prefix="P")
    return kd.kernel.axiom(
        smt.Implies(
            smt.And(
                smt.ForAll([n], n <= 0, P[n], P[n - 1]),
                P(0),
                smt.ForAll([n], n >= 0, P[n], P[n + 1]),
            ),
            # ---------------------------------------------------
            P(x),
        ),
        by="integer_induction",
    )


induct.register(smt.IntSort(), induct_int)


to_int = SortDispatch(name="to_int")
"""Sort based dispatch for `to_int`"""
smt.ExprRef.to_int = lambda x: to_int(x)  # type: ignore

to_real = SortDispatch(name="to_real")
"""Sort based dispatch for `to_real`"""
smt.ExprRef.to_real = lambda x: to_real(x)  # type: ignore


def QImplies(*hyp_conc) -> smt.BoolRef:
    """Quantified Implies

    Shorthand for `Implies(And(hyp[0], hyp[1], ...), conc)`

    >>> x,y = smt.Ints("x y")
    >>> QImplies(x > 0, y > 0, x + y > 0)
    Implies(And(x > 0, y > 0), x + y > 0)

    """
    conc = hyp_conc[-1]
    hyps = hyp_conc[:-1]
    if len(hyps) == 0:
        raise ValueError("No hypotheses given in QImplies", conc)
    elif len(hyps) == 1:
        return smt.Implies(hyps[0], conc)
    else:
        hyp = smt.And(hyps)
        return smt.Implies(hyp, conc)


def QForAll(vs: list[smt.ExprRef], *hyp_conc) -> smt.BoolRef:
    """Quantified ForAll

    Shorthand for `ForAll(vars, Implies(And(hyp[0], hyp[1], ...), conc))`

    If variables have a property `wf` attached, this is added as a hypothesis.

    There is no downside to always using this compared to `smt.ForAll` and it can avoid some errors.

    >>> x,y = smt.Ints("x y")
    >>> QForAll([x,y], x > 0, y > 0, x + y > 0)
    ForAll([x, y], Implies(And(x > 0, y > 0), x + y > 0))

    """
    conc = hyp_conc[-1]
    hyps = [v.assumes for v in vs if v.assumes is not None]
    hyps.extend([v.wf() for v in vs if v.sort() in wf.methods])
    hyps.extend(hyp_conc[:-1])
    if len(hyps) == 0:
        return smt.RawForAll(vs, conc)
    elif len(hyps) == 1:
        return smt.RawForAll(vs, smt.Implies(hyps[0], conc))
    else:
        hyp = smt.And(hyps)
        return smt.RawForAll(vs, smt.Implies(hyp, conc))


def QExists(vs: list[smt.ExprRef], *concs0) -> smt.BoolRef:
    """Quantified Exists

    Shorthand for `ForAll(vars, And(conc[0], conc[1], ...))`

    If variables have a property `wf` attached, this is anded into the properties.
    """
    concs = [v.assumes for v in vs if v.assumes is not None]
    concs.extend([v.wf() for v in vs if v.sort() in wf.methods])
    concs.extend(concs0)
    if len(concs) == 1:
        return smt.RawExists(vs, concs[0])
    else:
        return smt.RawExists(vs, smt.And(concs))


def QLambda(xs: list[smt.ExprRef], *args):
    """
    Conditional Lambda. If conjunction of conditions are not met, returns unconstrained value.

    >>> x = smt.Int("x")
    >>> QLambda([x], x > 0, x + 1)
    Lambda(x, If(x > 0, x + 1, f!...(x)))
    >>> QLambda([x], x > 0, x < 10, x + 1)
    Lambda(x, If(And(x > 0, x < 10), x + 1, f!...(x)))
    """
    conds, body = args[:-1], args[-1]
    undef = smt.FreshFunction(*[x.sort() for x in xs], body.sort())
    if len(conds) == 0:
        return smt.Lambda(xs, body)
    elif len(conds) == 1:
        return smt.Lambda(xs, smt.If(conds[0], body, undef(*xs)))
    else:
        return smt.Lambda(xs, smt.If(smt.And(conds), body, undef(*xs)))


def ExistsUnique(v: smt.ExprRef, *concs) -> smt.BoolRef:
    """Unique Existence"""
    y: smt.ExprRef = smt.FreshConst(v.sort(), prefix="y")
    concs_y = [smt.substitute(conc, (v, y)) for conc in concs]
    return smt.And(
        QExists([v], *concs),
        QForAll([v, y], *concs, *concs_y, v == y),
    )


def cond(*cases, default=None) -> smt.ExprRef:
    """
    Helper for chained ifs defined by cases.
    Each case is a tuple of a bool condition and a term.
    If default is not given, a check is performed for totality.

    >>> x = smt.Int("x")
    >>> kd.cond((x < 0, 2 * x), (x == 0, 3 * x), (x > 0, 5 * x))
    If(x < 0,
       2*x,
       If(x == 0, 3*x, If(x > 0, 5*x, unreachable...)))
    >>> kd.cond((x < 0, 2 * x), (x == 0, 3 * x), default = 5 * x)
    If(x < 0, 2*x, If(x == 0, 3*x, 5*x))
    """
    sort = None
    if default is not None and isinstance(default, smt.ExprRef):
        sort = default.sort()
    else:
        for c, t in cases:
            if not smt.is_bool(c):
                raise Exception("Condition must be boolean", c)
            if isinstance(
                t, smt.ExprRef
            ):  # looping through allows (some_cond , 0) to be a case if z3 will infer what 0 will be
                sort = t.sort()
                break
        if sort is None:
            raise Exception("Could not infer return sort")
    if default is None:
        """ Check totality of cases """
        s = smt.Solver()
        s.add(smt.Not(smt.Or([c for c, t in cases])))
        res = s.check()
        if res == smt.sat:
            raise Exception("Cases not exhaustive. Fix or give default", s.model())
        elif res != smt.unsat:
            raise Exception("Solver error. Give default", res)
        else:
            default = smt.FreshConst(sort, prefix="unreachable")
    acc = default
    for c, t in reversed(cases):
        if isinstance(t, smt.ExprRef) and t.sort() != sort:
            raise Exception("Sort mismatch in cond", t, sort)
        acc = smt.If(c, t, acc)
    return acc


def conde(*cases):
    """
    Minikanren style helper to create an `Or` of `And`s

    >>> x,y = smt.Ints("x y")
    >>> conde((x > 0, y == x + 1), (x < 0, y == x - 1))
    Or(And(x > 0, y == x + 1), And(x < 0, y == x - 1))
    """
    return smt.Or([smt.And(c) for c in cases])


class Cond:
    """
    Imperative class based API to build a chain of if-else statements
    """

    def __init__(self):
        self.cases = []
        self.default = None

    def when(self, cond: smt.BoolRef):
        self.cases.append((cond, None))
        return self

    def then(self, thn: smt.ExprRef):
        self.cases[-1] = (self.cases[-1][0], thn)
        return self

    def otherwise(self, els: smt.ExprRef):
        self.default = els
        return self

    def expr(self) -> smt.ExprRef:
        return cond(*self.cases, default=self.default)
