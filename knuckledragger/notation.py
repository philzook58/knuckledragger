"""Importing this module will add some syntactic sugar to Z3.

- Expr overload by single dispatch
- Bool supports `&`, `|`, `~`
- Sorts supports `>>` for ArraySort
- Datatypes support accessor notation
"""

import z3
import knuckledragger as kd

z3.BoolRef.__and__ = lambda self, other: z3.And(self, other)
z3.BoolRef.__or__ = lambda self, other: z3.Or(self, other)
z3.BoolRef.__invert__ = lambda self: z3.Not(self)


def QForAll(vs, *hyp_conc):
    """Quantified ForAll

    Shorthand for `ForAll(vars, Implies(And(hyp[0], hyp[1], ...), conc))`

    If variables have a property `wf` attached, this is added as a hypothesis.

    """
    conc = hyp_conc[-1]
    hyps = hyp_conc[:-1]
    hyps = [v.wf for v in vs if hasattr(v, "wf")] + list(hyps)
    if len(hyps) == 0:
        return z3.ForAll(vs, conc)
    elif len(hyps) == 1:
        return z3.ForAll(vs, z3.Implies(hyps[0], conc))
    else:
        hyp = z3.And(hyps)
        return z3.ForAll(vs, z3.Implies(hyp, conc))


def QExists(vs, *concs):
    """Quantified Exists

    Shorthand for `ForAll(vars, And(conc[0], conc[1], ...))`

    If variables have a property `wf` attached, this is anded into the properties.
    """
    concs = [v.wf for v in vs if hasattr(v, "wf")] + list(concs)
    if len(concs) == 1:
        z3.Exists(vars, concs[0])
    else:
        z3.Exists(vars, z3.And(concs))


z3.SortRef.__rshift__ = lambda self, other: z3.ArraySort(self, other)


class SortDispatch:
    """
    Sort dispatch is modeled after functools.singledispatch
    It allows for dispatching on the sort of the first argument
    """

    def __init__(self, default=None, name=None):
        self.methods = {}
        self.default = default
        self.name = name

    def register(self, sort, func):
        self.methods[sort] = func

    def __call__(self, *args, **kwargs):
        return self.methods.get(args[0].sort(), self.default)(*args, **kwargs)

    def define(self, args, body):
        assert isinstance(self.name, str)
        defn = kd.define(self.name, args, body)
        self.register(args[0].sort(), defn)
        return defn


add = SortDispatch(z3.ArithRef.__add__, name="add")
z3.ExprRef.__add__ = lambda x, y: add(x, y)

sub = SortDispatch(z3.ArithRef.__sub__, name="sub")
z3.ExprRef.__sub__ = lambda x, y: sub(x, y)

mul = SortDispatch(z3.ArithRef.__mul__, name="mul")
z3.ExprRef.__mul__ = lambda x, y: mul(x, y)

neg = SortDispatch(z3.ArithRef.__neg__, name="neg")
z3.ExprRef.__neg__ = lambda x: neg(x)

div = SortDispatch(z3.ArithRef.__div__, name="div")
z3.ExprRef.__truediv__ = lambda x, y: div(x, y)

and_ = SortDispatch()
z3.ExprRef.__and__ = lambda x, y: and_(x, y)

or_ = SortDispatch()
z3.ExprRef.__or__ = lambda x, y: or_(x, y)

lt = SortDispatch(z3.ArithRef.__lt__, name="lt")
z3.ExprRef.__lt__ = lambda x, y: lt(x, y)

le = SortDispatch(z3.ArithRef.__le__, name="le")
z3.ExprRef.__le__ = lambda x, y: le(x, y)


def lookup_cons_recog(self, k):
    """
    Enable "dot" syntax for fields of z3 datatypes
    """
    sort = self.sort()
    recog = "is_" == k[:3] if len(k) > 3 else False
    for i in range(sort.num_constructors()):
        cons = sort.constructor(i)
        if recog:
            if cons.name() == k[3:]:
                recog = sort.recognizer(i)
                return recog(self)
        else:
            for j in range(cons.arity()):
                acc = sort.accessor(i, j)
                if acc.name() == k:
                    return acc(self)


z3.DatatypeRef.__getattr__ = lookup_cons_recog


def Record(name, *fields):
    """
    Define a record datatype
    """
    rec = z3.Datatype(name)
    rec.declare("mk", *fields)
    rec = rec.create()
    return rec


class Cond:
    """
    Cond is a useful way to build up giant if-then-else expressions.
    """

    def __init__(self):
        self.clauses = []
        self.cur_case = None
        self.other = None
        self.sort = None
        self.default = None

    def when(self, c: z3.BoolRef) -> "Cond":
        assert self.cur_case is None
        assert isinstance(c, z3.BoolRef)
        self.cur_case = c
        return self

    def then(self, e: z3.ExprRef) -> "Cond":
        assert self.cur_case is not None
        if self.sort is not None:
            assert e.sort() == self.sort
        else:
            self.sort = e.sort()
        self.clauses.append((self.cur_case, e))
        self.cur_case = None
        return self

    def otherwise(self, e: z3.ExprRef) -> z3.ExprRef:
        assert self.default is None
        assert self.sort == e.sort()
        self.default = e
        return self.expr()

    def expr(self) -> z3.ExprRef:
        assert self.default is not None
        assert self.cur_case is None
        acc = self.default
        for c, e in reversed(self.clauses):
            acc = z3.If(c, e, acc)
        return acc
