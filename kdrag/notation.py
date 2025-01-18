"""
The `SortDispatch` system enables z3 sort based dispatch akin to ` functools.singledispatch`.
This is the mechanism for operator overloading in knuckledragger.

A special overloadable operation is the "well-formed" predicate `wf`.
Using the QForAll and QExists quantifiers will automatically insert `wf` calls for the appropriate sorts.
In this way, we can achieve an effect similar to refinement types.

Importing this module will add some syntactic sugar to smt.

- Expr overload by single dispatch
- Bool supports `&`, `|`, `~`
- Sorts supports `>>` for ArraySort
- Datatypes support accessor notation `l.is_cons`, `l.hd`, `l.tl` etc.
"""

import kdrag.smt as smt
import kdrag as kd
import typing

smt.BoolRef.__and__ = lambda self, other: smt.And(self, other)
smt.BoolRef.__or__ = lambda self, other: smt.Or(self, other)
smt.BoolRef.__invert__ = lambda self: smt.Not(self)


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

    def __init__(self, name=None, default=None):
        self.methods = {}
        self.default = default
        self.name = name

    def register(self, sort, func):
        self.methods[sort] = func

    def __getitem__(self, sort):
        return self.methods[sort]

    def __call__(self, *args, **kwargs):
        sort = args[0].sort()
        res = self.methods.get(sort, self.default)
        if res is None:
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


add = SortDispatch(name="add")
"""Sort based dispatch for `+` syntax"""
smt.ExprRef.__add__ = lambda x, y: add(x, y)  # type: ignore

radd = SortDispatch(name="radd")
"""Sort based dispatch for `+` syntax"""
smt.ExprRef.__radd__ = lambda x, y: radd(x, y)  # type: ignore

sub = SortDispatch(name="sub")
"""Sort based dispatch for `-` syntax"""
smt.ExprRef.__sub__ = lambda x, y: sub(x, y)  # type: ignore

mul = SortDispatch(name="mul")
"""Sort based dispatch for `*` syntax"""
smt.ExprRef.__mul__ = lambda x, y: mul(x, y)  # type: ignore

rmul = SortDispatch(name="rmul")
"""Sort based dispatch for `*` syntax"""
smt.ExprRef.__rmul__ = lambda x, y: rmul(x, y)  # type: ignore

matmul = SortDispatch(name="matmul")
"""Sort based dispatch for `@` syntax"""
smt.ExprRef.__matmul__ = lambda x, y: matmul(x, y)  # type: ignore

neg = SortDispatch(name="neg")
"""Sort based dispatch for `-` syntax"""
smt.ExprRef.__neg__ = lambda x: neg(x)  # type: ignore

div = SortDispatch(name="div_")
"""Sort based dispatch for `/` syntax"""
smt.ExprRef.__truediv__ = lambda x, y: div(x, y)  # type: ignore

and_ = SortDispatch(name="and_")
"""Sort based dispatch for `&` syntax"""
smt.ExprRef.__and__ = lambda x, y: and_(x, y)  # type: ignore

or_ = SortDispatch(name="or_")
"""Sort based dispatch for `|` syntax"""
smt.ExprRef.__or__ = lambda x, y: or_(x, y)  # type: ignore

invert = SortDispatch(name="invert")
"""Sort based dispatch for `~` syntax"""
smt.ExprRef.__invert__ = lambda x: invert(x)  # type: ignore

lt = SortDispatch(name="lt")
"""Sort based dispatch for `<` syntax"""
smt.ExprRef.__lt__ = lambda x, y: lt(x, y)  # type: ignore

le = SortDispatch(name="le")
"""Sort based dispatch for `<=` syntax"""
smt.ExprRef.__le__ = lambda x, y: le(x, y)  # type: ignore


wf = SortDispatch(name="wf")
"""`wf` is a special predicate for well-formedness. It is auto inserted by QForAll and QExists."""
smt.ExprRef.wf = lambda x: wf(x)  # type: ignore

induct = SortDispatch(name="induct")
"""Sort based dispatch for induction principles. Should instantiate an induction scheme for variable x and predicate P"""
smt.ExprRef.induct = lambda x, P: induct(x, P)  # type: ignore

getitem = SortDispatch(name="getitem")
"""Sort based dispatch for `[]` getitem syntax"""
smt.ExprRef.__getitem__ = lambda x, y: getitem(x, y)  # type: ignore


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
    hyps = hyp_conc[:-1]
    hyps = [v.wf() for v in vs if v.sort() in wf.methods] + list(hyps)
    if len(hyps) == 0:
        return smt.ForAll(vs, conc)
    elif len(hyps) == 1:
        return smt.ForAll(vs, smt.Implies(hyps[0], conc))
    else:
        hyp = smt.And(hyps)
        return smt.ForAll(vs, smt.Implies(hyp, conc))


def QExists(vs: list[smt.ExprRef], *concs) -> smt.BoolRef:
    """Quantified Exists

    Shorthand for `ForAll(vars, And(conc[0], conc[1], ...))`

    If variables have a property `wf` attached, this is anded into the properties.
    """
    concs = [v.wf() for v in vs if v.sort() in wf.methods] + list(concs)
    if len(concs) == 1:
        return smt.Exists(vs, concs[0])
    else:
        return smt.Exists(vs, smt.And(concs))


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
