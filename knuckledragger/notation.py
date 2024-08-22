"""Importing this module will add some syntactic sugar to smt.

- Expr overload by single dispatch
- Bool supports `&`, `|`, `~`
- Sorts supports `>>` for ArraySort
- Datatypes support accessor notation
"""

import knuckledragger.smt as smt
import knuckledragger as kd

smt.BoolRef.__and__ = lambda self, other: smt.And(self, other)
smt.BoolRef.__or__ = lambda self, other: smt.Or(self, other)
smt.BoolRef.__invert__ = lambda self: smt.Not(self)


smt.SortRef.__rshift__ = lambda self, other: smt.ArraySort(self, other)


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


add = SortDispatch(smt.ArithRef.__add__, name="add")
smt.ExprRef.__add__ = lambda x, y: add(x, y)

sub = SortDispatch(smt.ArithRef.__sub__, name="sub")
smt.ExprRef.__sub__ = lambda x, y: sub(x, y)

mul = SortDispatch(smt.ArithRef.__mul__, name="mul")
smt.ExprRef.__mul__ = lambda x, y: mul(x, y)

neg = SortDispatch(smt.ArithRef.__neg__, name="neg")
smt.ExprRef.__neg__ = lambda x: neg(x)

div = SortDispatch(smt.ArithRef.__div__, name="div_")
smt.ExprRef.__truediv__ = lambda x, y: div(x, y)

and_ = SortDispatch()
smt.ExprRef.__and__ = lambda x, y: and_(x, y)

or_ = SortDispatch()
smt.ExprRef.__or__ = lambda x, y: or_(x, y)

lt = SortDispatch(smt.ArithRef.__lt__, name="lt")
smt.ExprRef.__lt__ = lambda x, y: lt(x, y)

le = SortDispatch(smt.ArithRef.__le__, name="le")
smt.ExprRef.__le__ = lambda x, y: le(x, y)


wf = SortDispatch(name="wf")
smt.ExprRef.wf = lambda x: wf(x)


def QForAll(vs, *hyp_conc):
    """Quantified ForAll

    Shorthand for `ForAll(vars, Implies(And(hyp[0], hyp[1], ...), conc))`

    If variables have a property `wf` attached, this is added as a hypothesis.

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


def QExists(vs, *concs):
    """Quantified Exists

    Shorthand for `ForAll(vars, And(conc[0], conc[1], ...))`

    If variables have a property `wf` attached, this is anded into the properties.
    """
    concs = [v.wf() for v in vs if v.sort() in wf.methods] + list(concs)
    if len(concs) == 1:
        smt.Exists(vars, concs[0])
    else:
        smt.Exists(vars, smt.And(concs))


def lookup_cons_recog(self, k):
    """
    Enable "dot" syntax for fields of smt datatypes
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


smt.DatatypeRef.__getattr__ = lookup_cons_recog


def datatype_call(self, *args):
    """
    Enable "call" syntax for constructors of smt datatypes
    """
    # TODO: could also enable keyword syntax
    assert self.num_constructors() == 1
    return self.constructor(0)(*args)


smt.DatatypeSortRef.__call__ = datatype_call


def Record(name, *fields, pred=None):
    """
    Define a record datatype
    """
    rec = smt.Datatype(name)
    rec.declare(name, *fields)
    rec = rec.create()
    rec.mk = rec.constructor(0)
    if pred is not None:
        wf.register(rec, lambda x: pred(x))
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

    def when(self, c: smt.BoolRef) -> "Cond":
        assert self.cur_case is None
        assert isinstance(c, smt.BoolRef)
        self.cur_case = c
        return self

    def then(self, e: smt.ExprRef) -> "Cond":
        assert self.cur_case is not None
        if self.sort is not None:
            assert e.sort() == self.sort
        else:
            self.sort = e.sort()
        self.clauses.append((self.cur_case, e))
        self.cur_case = None
        return self

    def otherwise(self, e: smt.ExprRef) -> smt.ExprRef:
        assert self.default is None
        assert self.sort == e.sort()
        self.default = e
        return self.expr()

    def expr(self) -> smt.ExprRef:
        assert self.default is not None
        assert self.cur_case is None
        acc = self.default
        for c, e in reversed(self.clauses):
            acc = smt.If(c, e, acc)
        return acc
