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

smt.BoolRef.__and__ = lambda self, other: smt.And(self, other)
smt.BoolRef.__or__ = lambda self, other: smt.Or(self, other)
smt.BoolRef.__invert__ = lambda self: smt.Not(self)


smt.SortRef.__rshift__ = lambda self, other: smt.ArraySort(self, other)

smt.ArrayRef.__call__ = lambda self, arg: self[arg]


class SortDispatch:
    """
    Sort dispatch is modeled after functools.singledispatch
    It allows for dispatching on the sort of the first argument
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
        res = self.methods.get(args[0].sort(), self.default)
        if res is None:
            raise NotImplementedError()
        return res(*args, **kwargs)

    def define(self, args, body):
        assert isinstance(self.name, str)
        defn = kd.define(self.name, args, body)
        self.register(args[0].sort(), defn)
        return defn


add = SortDispatch(name="add")
smt.ExprRef.__add__ = lambda x, y: add(x, y)

radd = SortDispatch(name="radd")
smt.ExprRef.__radd__ = lambda x, y: radd(x, y)

sub = SortDispatch(name="sub")
smt.ExprRef.__sub__ = lambda x, y: sub(x, y)

mul = SortDispatch(name="mul")
smt.ExprRef.__mul__ = lambda x, y: mul(x, y)

rmul = SortDispatch(name="rmul")
smt.ExprRef.__rmul__ = lambda x, y: rmul(x, y)

matmul = SortDispatch(name="matmul")
smt.ExprRef.__matmul__ = lambda x, y: matmul(x, y)

neg = SortDispatch(name="neg")
smt.ExprRef.__neg__ = lambda x: neg(x)

div = SortDispatch(name="div_")
smt.ExprRef.__truediv__ = lambda x, y: div(x, y)

and_ = SortDispatch()
smt.ExprRef.__and__ = lambda x, y: and_(x, y)

or_ = SortDispatch()
smt.ExprRef.__or__ = lambda x, y: or_(x, y)

invert = SortDispatch(name="invert")
smt.ExprRef.__invert__ = lambda x: invert(x)

lt = SortDispatch(name="lt")
smt.ExprRef.__lt__ = lambda x, y: lt(x, y)

le = SortDispatch(name="le")
smt.ExprRef.__le__ = lambda x, y: le(x, y)


wf = SortDispatch(name="wf")
smt.ExprRef.wf = lambda x: wf(x)

induct = SortDispatch(name="induct")
smt.ExprRef.induct = lambda x: induct(x)

getitem = SortDispatch(name="getitem")
smt.ExprRef.__getitem__ = lambda x, y: getitem(x, y)


def QForAll(vs: list[smt.ExprRef], *hyp_conc) -> smt.BoolRef:
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


def _lookup_constructor_recog(self, k):
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


smt.DatatypeRef.__getattr__ = _lookup_constructor_recog


def datatype_call(self, *args):
    """
    Enable "call" syntax for constructors of smt datatypes
    """
    # TODO: could also enable keyword syntax
    assert self.num_constructors() == 1
    return self.constructor(0)(*args)


smt.DatatypeSortRef.__call__ = datatype_call

records = {}


def Record(name: str, *fields, pred=None) -> smt.DatatypeSortRef:
    """
    Define a record datatype.
    The optional argument `pred` will add a well-formedness condition to the record
    giving something akin to a refinement type.
    """
    if name in records:
        raise Exception("Record already defined", name)
    rec = smt.Datatype(name)
    rec.declare(name, *fields)
    rec = rec.create()
    rec.mk = rec.constructor(0)
    wf_cond = [n for (n, (_, sort)) in enumerate(fields) if sort in wf.methods]
    if pred is None and len(wf_cond) == 1:
        acc = rec.accessor(0, wf_cond[0])
        wf.register(rec, lambda x: rec.accessor(0, acc(x).wf()))
    elif pred is None and len(wf_cond) > 1:
        wf.register(
            rec, lambda x: smt.And(*[rec.accessor(0, n)(x).wf() for n in wf_cond])
        )
    elif pred is not None and len(wf_cond) == 0:
        wf.register(rec, lambda x: pred(x))
    elif pred is not None and len(wf_cond) > 0:
        wf.register(
            rec,
            lambda x: smt.And(pred(x), *[rec.accessor(0, n)(x).wf() for n in wf_cond]),
        )
    records[name] = rec

    return rec


def NewType(name: str, sort: smt.SortRef, pred=None) -> smt.DatatypeSortRef:
    """Minimal wrapper around a sort for sort based overloading"""
    return Record(name, ("val", sort), pred=pred)


def induct_inductive(DT: smt.DatatypeSortRef, x=None, P=None) -> kd.kernel.Proof:
    """Build a basic induction principle for an algebraic datatype"""
    if P is None:
        P = smt.FreshConst(smt.ArraySort(DT, smt.BoolSort()), prefix="P")
    hyps = []
    for i in range(DT.num_constructors()):
        constructor = DT.constructor(i)
        args = [
            smt.FreshConst(constructor.domain(j), prefix="a")
            for j in range(constructor.arity())
        ]
        acc = P(constructor(*args))
        for arg in args:
            if arg.sort() == DT:
                acc = kd.QForAll([arg], P(arg), acc)
            else:
                acc = kd.QForAll([arg], acc)
        hyps.append(acc)
    if x is None:
        x = smt.FreshConst(DT, prefix="x")
        conc = kd.QForAll([x], P(x))
    else:
        conc = P(x)
    if isinstance(P, smt.ExprRef):
        return kd.axiom(
            smt.ForAll([P], smt.Implies(smt.And(hyps), conc)), by="induction_axiom"
        )
    else:
        return kd.axiom(
            smt.ForAll([P], smt.Implies(smt.And(hyps), conc)), by="induction_axiom"
        )


def Inductive(name: str, strict=True) -> smt.DatatypeSortRef:
    """Declare datatypes with auto generated induction principles. Wrapper around z3.Datatype"""
    if strict and name in records:
        raise Exception(
            "Datatype with that name already defined. Use keyword strict=False to override",
            name,
            # records[name].sexpr(),
        )
    dt = smt.Datatype(name)
    oldcreate = dt.create

    def create():
        dt = oldcreate()
        # Sanity check no duplicate names. Causes confusion.
        if strict:
            names = set()
            for i in range(dt.num_constructors()):
                cons = dt.constructor(i)
                n = cons.name()
                if n in names:
                    raise Exception("Duplicate constructor name", n)
                names.add(n)
                for j in range(cons.arity()):
                    n = dt.accessor(i, j).name()
                    if n in names:
                        raise Exception("Duplicate field name", n)
                    names.add(n)
        x = smt.FreshConst(dt, prefix="x")
        kd.notation.induct.register(dt, lambda x: induct_inductive(dt, x=x))
        records[name] = dt
        return dt

    dt.create = create
    return dt


def cond(*cases, default=None) -> smt.ExprRef:
    """
    Helper for chained ifs defined by cases.
    Each case is a tuple of a bool condition and a term.
    If default is not given, a check is performed for totality.
    """
    sort = cases[0][1].sort()
    if default is None:
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
        if t.sort() != sort:
            raise Exception("Sort mismatch in cond", t, sort)
        acc = smt.If(c, t, acc)
    return acc


class Cond:
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
