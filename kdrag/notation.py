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
"""
`wf` is a special predicate for well-formedness. It is auto inserted by QForAll and QExists.
"""
smt.ExprRef.wf = lambda x: wf(x)

induct = SortDispatch(name="induct")
smt.ExprRef.induct = lambda x, P: induct(x, P)

getitem = SortDispatch(name="getitem")
smt.ExprRef.__getitem__ = lambda x, y: getitem(x, y)


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


def datatype_iter(self):
    return (self.constructor(i) for i in range(self.num_constructors()))


smt.DatatypeSortRef.__iter__ = datatype_iter


def datatype_len(self):
    return self.num_constructors()


smt.DatatypeSortRef.__len__ = datatype_len

records = {}


def Record(name: str, *fields, pred=None, admit=False) -> smt.DatatypeSortRef:
    """
    Define a record datatype.
    The optional argument `pred` will add a well-formedness condition to the record
    giving something akin to a refinement type.
    """
    if not admit and name in records:
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


def NewType(
    name: str, sort: smt.SortRef, pred=None, admit=False
) -> smt.DatatypeSortRef:
    """Minimal wrapper around a sort for sort based overloading"""
    return Record(name, ("val", sort), pred=pred, admit=admit)


def Enum(name, args, admit=False):
    """Shorthand for simple enumeration datatypes. Similar to python's Enum.
    >>> Color = Enum("Color", "Red Green Blue")
    >>> smt.And(Color.Red != Color.Green, Color.Red != Color.Blue)
    And(Red != Green, Red != Blue)
    """
    T = kd.Inductive(name, admit=admit)
    for c in args.split():
        T.declare(c)
    T = T.create()
    return T


"""
def induct_inductive(DT: smt.DatatypeSortRef, x=None, P=None) -> kd.kernel.Proof:
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
"""


def induct_inductive(x: smt.DatatypeRef, P: smt.QuantifierRef) -> kd.kernel.Proof:
    """Build a basic induction principle for an algebraic datatype"""
    DT = x.sort()
    assert isinstance(DT, smt.DatatypeSortRef)
    """assert (
        smt.is_quantifier(P) and P.is_lambda()
    )  # TODO: Hmm. Actually it should just be arraysort"""
    hyps = []
    for i in range(DT.num_constructors()):
        constructor = DT.constructor(i)
        args = [
            smt.FreshConst(constructor.domain(j), prefix=DT.accessor(i, j).name())
            for j in range(constructor.arity())
        ]
        acc = P(constructor(*args))
        for arg in args:
            if arg.sort() == DT:
                acc = kd.QForAll([arg], P(arg), acc)
            else:
                acc = kd.QForAll([arg], acc)
        hyps.append(acc)
    conc = P(x)
    return kd.axiom(smt.Implies(smt.And(hyps), conc), by="induction_axiom_schema")


def Inductive(name: str, admit=False) -> smt.Datatype:
    """Declare datatypes with auto generated induction principles. Wrapper around z3.Datatype"""
    if not admit and name in records:
        raise Exception(
            "Datatype with that name already defined. Use keyword admit=True to override",
            name,
            # records[name].sexpr(),
        )
    dt = smt.Datatype(name)
    oldcreate = dt.create

    def create():
        dt = oldcreate()
        # Sanity check no duplicate names. Causes confusion.
        if not admit:
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
        kd.notation.induct.register(dt, induct_inductive)
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
    return smt.Or([smt.And(c) for c in cases])


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
