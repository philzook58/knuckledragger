import kdrag.smt as smt
import kdrag as kd
import typing


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


smt.DatatypeRef.__getattr__ = _lookup_constructor_recog  # type: ignore


def datatype_call(self: smt.DatatypeSortRef, *args: smt.ExprRef) -> smt.DatatypeRef:
    """
    Enable "call" syntax for constructors of smt datatypes
    """
    # TODO: could also enable keyword syntax
    assert self.num_constructors() == 1
    return self.constructor(0)(*[smt._py2expr(a) for a in args])


smt.DatatypeSortRef.__call__ = datatype_call  # type: ignore
""" Call syntax for constructors of smt datatypes """


def datatype_replace(self: smt.DatatypeRef, **kwargs: smt.ExprRef) -> smt.DatatypeRef:
    """
    Like NamedTuple, you can replace fields of a record datatype.

    >>> Point = kd.Record("Point", ("x", smt.RealSort()), ("y", smt.RealSort()))
    >>> Point(0,1)._replace(x=3, y=10)
    Point(3, 10)
    >>> p = smt.Const("p", Point)
    >>> q = p._replace(y=10)
    >>> q
    Point(x(p), 10)
    >>> q._replace(x=1)
    Point(1, 10)
    """
    sort = self.sort()

    if sort.num_constructors() != 1:
        raise TypeError(
            "`_replace` is not supported on datatypes with multiple constructors"
        )

    cons = sort.constructor(0)
    accs = [sort.accessor(0, i) for i in range(cons.arity())]
    names = {acc.name() for acc in accs}  # Use a set for quick lookup

    invalid_fields = kwargs.keys() - names
    if invalid_fields:
        raise ValueError(
            f"Constructor `{cons.name()}` does not have fields: {', '.join(invalid_fields)}"
        )

    defaults = (
        self.children() if smt.is_constructor(self) else [acc(self) for acc in accs]
    )

    fields = [kwargs.get(acc.name(), default) for acc, default in zip(accs, defaults)]

    return cons(*fields)


smt.DatatypeRef._replace = datatype_replace  # type: ignore


def datatype_iter(self: smt.DatatypeSortRef) -> typing.Iterator[smt.DatatypeRef]:
    """Enable iteration over constructors of a datatype sort"""
    if any(self.constructor(i).arity() > 0 for i in range(self.num_constructors())):
        raise TypeError(
            "For Enum like datatypes. Cannot iterate over constructors with arguments"
        )
    return (self.constructor(i)() for i in range(self.num_constructors()))


smt.DatatypeSortRef.__iter__ = datatype_iter  # type: ignore


def datatype_len(self: smt.DatatypeSortRef) -> int:
    """Enable len() on datatype sorts"""
    return self.num_constructors()


smt.DatatypeSortRef.__len__ = datatype_len  # type: ignore

records = {}


def induct_inductive(x: smt.DatatypeRef, P: smt.QuantifierRef) -> kd.kernel.Proof:
    """Build a basic induction principle for an algebraic datatype"""
    DT = x.sort()
    assert isinstance(DT, smt.DatatypeSortRef)
    """assert (
        isisntance(P,QuantififerRef) and P.is_lambda()
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


def Inductive(name: str) -> smt.Datatype:
    """
    Declare datatypes with auto generated induction principles. Wrapper around z3.Datatype

    >>> Nat = Inductive("Nat")
    >>> Nat.declare("zero")
    >>> Nat.declare("succ", ("pred", Nat))
    >>> Nat = Nat.create()
    >>> Nat.succ(Nat.zero)
    succ(zero)
    """
    counter = 0
    n = name
    while n in records:
        counter += 1
        n = name + "!" + str(counter)
    name = n
    assert name not in records
    dt = smt.Datatype(name)
    oldcreate = dt.create

    def create():
        dt = oldcreate()
        # Sanity check no duplicate names. Causes confusion.
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


def Record(
    name: str, *fields: tuple[str, smt.SortRef], pred=None
) -> smt.DatatypeSortRef:
    """
    Define a record datatype.
    The optional argument `pred` will add a well-formedness condition to the record
    giving something akin to a refinement type.

    >>> Point = Record("Point", ("x", smt.RealSort()), ("y", smt.RealSort()))
    >>> Point(1,2)
    Point(ToReal(1), ToReal(2))
    >>> Point(1,2).x
    x(Point(ToReal(1), ToReal(2)))
    >>> PosPoint = Record("PosPoint", ("x", smt.RealSort()), ("y", smt.RealSort()), pred = lambda p: smt.And(p.x > 0, p.y > 0))
    >>> p = smt.Const("p", PosPoint)
    >>> kd.QForAll([p], p.x > -42)
    ForAll(p, Implies(And(x(p) > 0, y(p) > 0), x(p) > -42))
    """
    rec = Inductive(name)
    rec.declare(name, *fields)
    rec = rec.create()
    rec.mk = rec.constructor(0)
    wf_cond = [
        n for (n, (_, sort)) in enumerate(fields) if sort in kd.notation.wf.methods
    ]
    if pred is None and len(wf_cond) == 1:
        acc = rec.accessor(0, wf_cond[0])
        kd.notation.wf.register(rec, lambda x: rec.accessor(0, acc(x).wf()))
    elif pred is None and len(wf_cond) > 1:
        kd.notation.wf.register(
            rec, lambda x: smt.And(*[rec.accessor(0, n)(x).wf() for n in wf_cond])
        )
    elif pred is not None and len(wf_cond) == 0:
        kd.notation.wf.register(rec, lambda x: pred(x))
    elif pred is not None and len(wf_cond) > 0:
        kd.notation.wf.register(
            rec,
            lambda x: smt.And(pred(x), *[rec.accessor(0, n)(x).wf() for n in wf_cond]),
        )

    return rec


def NewType(name: str, sort: smt.SortRef, pred=None) -> smt.DatatypeSortRef:
    """Minimal wrapper around a sort for sort based overloading

    >>> NatI = NewType("NatI", smt.IntSort(), pred = lambda x: x.val >= 0)
    >>> x = smt.Const("x", NatI)
    >>> kd.QForAll([x], x.val >= -7)
    ForAll(x, Implies(val(x) >= 0, val(x) >= -7))
    """
    return Record(name, ("val", sort), pred=pred)


def Enum(name: str, args: str) -> smt.DatatypeSortRef:
    """Shorthand for simple enumeration datatypes. Similar to python's Enum.
    >>> Color = Enum("Color", "Red Green Blue")
    >>> smt.And(Color.Red != Color.Green, Color.Red != Color.Blue)
    And(Red != Green, Red != Blue)
    """
    T = kd.Inductive(name)
    for c in args.split():
        T.declare(c)
    T = T.create()
    return T


rel = kd.notation.SortDispatch(name="rel")
"""The relation associated with a Datatype of evidence"""
smt.DatatypeRef.rel = lambda *args: rel(*args)


def InductiveRel(name: str, *params: smt.ExprRef) -> smt.Datatype:
    """Define an inductive type of evidence and a relation the recurses on that evidence

    >>> x = smt.Int("x")
    >>> Even = InductiveRel("Even", x)
    >>> Even.declare("Ev_Z",                           pred = x == 0)
    >>> Even.declare("Ev_SS", ("sub2_evidence", Even), pred = lambda evid: evid.rel(x-2))
    >>> Even = Even.create()
    >>> smt.Const("ev", Even).rel(4)
    even(ev, 4)
    """

    dt = Inductive(name)

    relname = name.lower()
    olddeclare = dt.declare
    preds = []  # tuck away extra predicate

    def declare(
        name, *args, pred=None
    ):  # TODO: would it ever make sense to not have a pred?
        olddeclare(name, *args)
        preds.append(pred)

    dt.declare = declare

    oldcreate = dt.create

    def create_relation(dt):
        """
        When inductive is done being defined, call this function
        """
        ev = smt.FreshConst(dt, prefix=name.lower())
        rel = smt.Function(relname, dt, *[x.sort() for x in params], smt.BoolSort())
        cases = []
        for i in range(dt.num_constructors()):
            precond = dt.recognizer(i)(ev)  # recognize case of the evidence
            pred = preds[i]  # In this case, this predicate should be true
            if pred is None:
                res = smt.BoolVal(True)
            elif isinstance(pred, smt.ExprRef):
                res = pred
            else:
                args = [dt.accessor(i, j)(ev) for j in range(dt.constructor(i).arity())]
                res = pred(*args)
            cases.append((precond, res))
        args = [ev]
        args.extend(params)
        rel = kd.define(relname, args, kd.cond(*cases))
        return rel

    def create():
        dt = oldcreate()
        dtrel = smt.Function(relname, dt, *[x.sort() for x in params], smt.BoolSort())
        rel.register(
            dt, lambda *args: dtrel(*args)
        )  # doing this here let's us tie the knot inside of lambdas and refer to the predicate.
        dtrel = create_relation(dt)
        dt.rel = dtrel
        return dt

    dt.create = create
    return dt
