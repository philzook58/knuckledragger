"""
Convenience features for datatypes.

You should use these instead of raw `smt.Datatype`. This also maintains a record of existing datatypes
so that you don't clobber old ones, a possible source of unsoundness.

- Datatypes support accessor notation `l.is_cons`, `l.hd`, `l.tl` etc.
- x._replace() syntax on single constructor datatypes

>>> import kdrag.theories.nat as nat
>>> n = smt.Const("n", nat.Nat)
>>> n.is_Z
is(Z, n)
>>> n.pred
pred(n)
>>> kd.prove(nat.one.pred == nat.Z)
|= pred(S(Z)) == Z
"""

import kdrag.smt as smt
import kdrag as kd
import typing
from kdrag.kernel import Inductive


def _lookup_constructor_recog(
    self: smt.DatatypeRef, k: str
) -> typing.Optional[smt.ExprRef]:
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


def constructor_num(s: smt.DatatypeSortRef, k: str) -> int:
    for i in range(s.num_constructors()):
        cons = s.constructor(i)
        if cons.name() == k:
            return i
    raise ValueError(f"Constructor {k} not found in datatype {s}")


def accessor_num(s: smt.DatatypeSortRef, constr_num: int, k: str) -> int:
    cons = s.constructor(constr_num)
    for j in range(cons.arity()):
        acc = s.accessor(constr_num, j)
        if acc.name() == k:
            return j
    raise ValueError(f"Accessor {k} not found in constructor {cons} of datatype {s}")


call_dict: dict[smt.SortRef, typing.Callable] = {}
"""A registry for overloadable call on datatypes"""


def datatype_call(
    self: smt.DatatypeSortRef, *args: smt.ExprRef, **kwargs
) -> smt.DatatypeRef:
    """
    Enable "call" syntax for constructors of smt datatypes

    >>> Point = kd.Struct("Point", ("x", smt.IntSort()), ("y", smt.IntSort()))
    >>> Point(1,2)
    Point(1, 2)
    >>> Point(y=2, x=1)
    Point(1, 2)
    """
    f = call_dict.get(self, None)
    if f is not None:
        return f(*args, **kwargs)
    else:  # default
        # TODO: could also enable keyword syntax
        assert self.num_constructors() == 1
        cons = self.constructor(0)
        if len(kwargs) == 0:
            return cons(*[smt._py2expr(a) for a in args])
        elif len(args) == 0:
            args1 = [None] * cons.arity()
            for k, v in kwargs.items():
                j = accessor_num(self, 0, k)
                args1[j] = v
            assert all(a is not None for a in args)
            return cons(*args1)
        else:
            raise TypeError("Cannot mix positional and keyword arguments")


smt.DatatypeSortRef.__call__ = datatype_call  # type: ignore
""" Call syntax for constructors of smt datatypes """


def datatype_replace(self: smt.DatatypeRef, **kwargs: smt.ExprRef) -> smt.DatatypeRef:
    """
    Like NamedTuple, you can replace fields of a record datatype.

    >>> Point = kd.Struct("Point", ("x", smt.RealSort()), ("y", smt.RealSort()))
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
        raise TypeError("Cannot iterate over constructors with arguments")
    return (self.constructor(i)() for i in range(self.num_constructors()))


smt.DatatypeSortRef.__iter__ = datatype_iter  # type: ignore


def datatype_len(self: smt.DatatypeSortRef) -> int:
    """Enable len() on datatype sorts. Returns the number of constructors"""
    return self.num_constructors()


smt.DatatypeSortRef.__len__ = datatype_len  # type: ignore


def pattern_match(
    x: smt.DatatypeRef, pat: smt.DatatypeRef
) -> tuple[list[smt.BoolRef], dict[smt.DatatypeRef, smt.DatatypeRef]]:
    """
    A Symbolic execution of sorts of pattern matching.
    Returns the constraints and substitutions for variables

    >>> import kdrag.theories.nat as nat
    >>> n,m = smt.Consts("n m", nat.Nat)
    >>> pattern_match(n, nat.S(nat.S(m)))
    ([is(S, n), is(S, pred(n))], {m: pred(pred(n))})
    """
    subst = {}
    constraints = []
    todo = [(x, pat)]
    while todo:
        x, pat = todo.pop()
        if smt.is_constructor(pat):
            dt = pat.sort()
            decl = pat.decl()
            i = 0
            for i in range(dt.num_constructors()):
                # figure out which constructor
                if decl == dt.constructor(i):
                    break
            constraints.append(dt.recognizer(i)(x))
            for j, subpat in enumerate(pat.children()):
                todo.append((dt.accessor(i, j)(x), subpat))
        elif (
            smt.is_int_value(pat)
            or smt.is_true(pat)
            or smt.is_false(pat)
            or smt.is_rational_value(pat)
        ):  # or smt.is_real_value(pat) or smt.is_true(pat) or smt.is_false(pat):
            constraints.append(x == pat)
        elif smt.is_const(pat):  # possible variable
            if pat.decl() in kd.kernel.defns:  # actually a defined constant
                constraints.append(x == pat)
            elif pat in subst:
                constraints.append(x == subst[pat])  # non-linear patterns
                subst[pat] = x
            else:
                subst[pat] = x
        else:
            raise ValueError("Not a supported pattern", pat)
    return constraints, subst


def multipattern_match(
    *cases: tuple[smt.DatatypeRef, smt.DatatypeRef],
) -> tuple[list[smt.BoolRef], dict[smt.DatatypeRef, smt.DatatypeRef]]:
    subst = {}
    constraints = []
    for x, pat in cases:
        constr, subst2 = pattern_match(x, pat)
        constraints.extend(constr)
        subst = {**subst, **subst2}
    return constraints, subst


def define_primrec(fun_name, vs: list[smt.ExprRef], res_type: smt.SortRef, **cases):
    """
    Define a function by primitive recursion. https://en.wikipedia.org/wiki/Primitive_recursive_function
    This is the analog of a fold.

    >>> import kdrag.theories.nat as nat
    >>> n, m = smt.Consts("n m", nat.Nat)
    >>> myadd2 = define_primrec("myadd2", [n, m], nat.Nat, \
                                Z = lambda: m,\
                                S = lambda a: nat.S(a))
    >>> myadd2.defn
    |= ForAll([n, m],
        myadd2(n, m) == If(is(S, n), S(myadd2(pred(n), m)), m))
    """
    l = vs[0]
    assert isinstance(l, smt.DatatypeRef)
    params = vs[1:]
    sort = l.sort()
    f = smt.Function(fun_name, *[v.sort() for v in vs], res_type)
    acc = None
    for i in range(sort.num_constructors()):
        constr = sort.constructor(i)
        name = constr.name()
        args = [
            sort.accessor(i, j)(l)
            if constr.domain(j) != sort
            else f(sort.accessor(i, j)(l), *params)
            for j in range(constr.arity())
        ]
        if acc is None:
            acc = cases[name](*args)
        else:
            acc = smt.If(sort.recognizer(i)(l), cases[name](*args), acc)
        del cases[name]
    if len(cases) != 0:
        raise ValueError("unused cases", cases)
    assert isinstance(acc, smt.ExprRef)
    return kd.define(fun_name, vs, acc)


def define_fun(eqs):
    """
    Define a function by pattern matching equations.

    >>> import kdrag.theories.nat as nat
    >>> n, m = smt.Consts("n m", nat.Nat)
    >>> myadd = smt.Function("myadd", nat.Nat, nat.Nat, nat.Nat)
    >>> myadd = define_fun([myadd(nat.Z, m)    == m,\
                            myadd(nat.S(n), m) == nat.S(myadd(n, m))])
    >>> myadd.case0
    |= ForAll(m, myadd(Z, m) == m)
    >>> myadd.case1
    |= ForAll([n, m], myadd(S(n), m) == S(myadd(n, m)))
    """
    decl = eqs[0].arg(0).decl()
    cases = []  # For kd.define of kd.cond
    axs = []  # forall quantified form of equations
    args = [smt.FreshConst(decl.domain(i)) for i in range(decl.arity())]
    for n, eq in enumerate(eqs):
        if not smt.is_eq(eq):
            raise ValueError("Case is not an equality", n, eq)
        lhs, rhs = eq.children()

        if lhs.decl() != decl:
            raise ValueError(
                "Left-hand side does not match previous function declaration", lhs, decl
            )
        pats = lhs.children()

        # compute contraints implied by pattern
        constr, subst = kd.datatype.multipattern_match(*zip(args, pats))
        axs.append(smt.ForAll(list(subst.keys()), eq))
        cases.append((smt.And(constr), smt.substitute(rhs, *subst.items())))

        # simple structural termination check
        rec_calls = list(kd.utils.find_calls(decl, rhs))
        for call in rec_calls:
            # TODO: Could do fancier inference or termination criteria
            if not kd.utils.is_subterm(call.arg(0), pats[0]):
                raise ValueError(
                    "Recursive call not structurally recursive on first argument"
                )

    f = kd.kernel.define(decl.name(), args, kd.cond(*cases))
    for n, ax in enumerate(axs):
        # TODO: Hmm. Cases may not be mutually exclusive so this could fail.
        setattr(f, "case" + str(n), kd.kernel.prove(ax, by=[f.defn]))
    return f


def datatype_match_(x, *cases, default=None):
    """
    Pattern matching for datatypes.

    >>> import kdrag.theories.nat as nat
    >>> x = smt.Const("x", nat.Nat)
    >>> x.match_((nat.S(x), nat.S(x)), (nat.one, nat.one), default=x)
    If(is(S, x),
       S(pred(x)),
       If(And(is(S, x), is(Z, pred(x))), S(Z), x))

    >>> import kdrag.theories.list as list_
    >>> IntList = list_.List(smt.IntSort())
    >>> l = smt.Const("l", IntList.T)
    >>> x,y,z = smt.Ints("x y z")
    >>> l.match_((IntList.Nil, 0), (IntList.Cons(x, l), 1 + x))
    If(is(Nil, l),
       0,
       If(is(Cons, l), 1 + head(l), unreachable!...))

    """
    newcases = []
    for i, (pat, body) in enumerate(cases):
        constraints, subst = pattern_match(x, pat)
        if len(subst) > 0:
            body = smt.substitute(
                smt._py2expr(body), *[(v, e) for v, e in subst.items()]
            )
        if len(constraints) == 0:
            cond = smt.BoolVal(True)
        elif len(constraints) == 1:
            cond = constraints[0]
        else:
            cond = smt.And(constraints)
        newcases.append((cond, body))
    return kd.cond(*newcases, default=default)


smt.DatatypeRef.match_ = datatype_match_  # type: ignore


def Struct(
    name: str, *fields: tuple[str, smt.SortRef], pred=None
) -> smt.DatatypeSortRef:
    """
    Define a record datatype.
    This is the analog in many respects of python's NamedTuple.
    The optional argument `pred` will add a well-formedness condition to the record
    giving something akin to a refinement type.

    >>> Point = Struct("Point", ("x", smt.RealSort()), ("y", smt.RealSort()))
    >>> Point(1,2)
    Point(ToReal(1), ToReal(2))
    >>> Point(1,2).x
    x(Point(ToReal(1), ToReal(2)))
    >>> PosPoint = Struct("PosPoint", ("x", smt.RealSort()), ("y", smt.RealSort()), pred = lambda p: smt.And(p.x > 0, p.y > 0))
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
    return Struct(name, ("val", sort), pred=pred)


def Enum(name: str, args: str | list[str]) -> smt.DatatypeSortRef:
    """Shorthand for simple enumeration datatypes. Similar to python's Enum.
    >>> Color = Enum("Color", "Red Green Blue")
    >>> smt.And(Color.Red != Color.Green, Color.Red != Color.Blue)
    And(Red != Green, Red != Blue)
    """
    T = kd.Inductive(name)
    if isinstance(args, str):
        args = args.split()
    for c in args:
        T.declare(c)
    T = T.create()
    return T


rel = kd.notation.SortDispatch(name="rel")
"""SortDispatch for the relation associated with a Datatype of evidence"""
smt.DatatypeRef.rel = lambda *args: rel(*args)
# smt.DatatypeRef.rel = lambda self, *args: self.rel(*args)


def InductiveRel(name: str, *params: smt.ExprRef) -> smt.Datatype:
    """Define an inductive type of evidence and a relation the recurses on that evidence

    >>> x = smt.Int("x")
    >>> Even = InductiveRel("Even", x)
    >>> Even.declare("Ev_Z",                           pred = x == 0)
    >>> Even.declare("Ev_SS", ("sub2_evidence", Even), pred = lambda evid: evid.rel(x-2))
    >>> Even = Even.create()
    >>> ev = smt.Const("ev", Even)
    >>> ev.rel(4)
    even(4)[ev]
    >>> ev(4)
    even(4)[ev]
    >>> Even(4)
    even(4)
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
        rel = kd.define(relname, list(params), smt.Lambda([ev], kd.cond(*cases)))
        return rel

    def create():
        dt = oldcreate()
        if any(p is not None for p in preds):
            dtrel = smt.Function(
                relname, *[x.sort() for x in params], smt.ArraySort(dt, smt.BoolSort())
            )
            kd.notation.call.register(dt, lambda self, *args: dtrel(*args)[self])
            rel.register(
                dt, lambda self, *args: dtrel(*args)[self]
            )  # doing this here let's us tie the knot inside of lambdas and refer to the predicate.
            dtrel = create_relation(dt)
            dt.rel = dtrel
            # ev = smt.FreshConst(dt, prefix=name.lower())
            call_dict[dt] = dtrel  # lambda *args: smt.Lambda([ev], ev.rel(*args))

            if len(params) == 0:
                kd.notation.wf.register(dt, lambda x: x.rel())
        return dt

    dt.create = create
    return dt


def inj_lemmas(dt: smt.DatatypeSortRef) -> list[kd.kernel.Proof]:
    """
    Injectivity lemmas for a datatype. Z3 internally understands these, but can be useful to be explicit about them in some situations

    >>> import kdrag.theories.nat as nat
    >>> inj_lemmas(nat.Nat)[0]
    |= ForAll([x!..., y!...],
           (S(x!...) == S(y!...)) == And(x!... == y!...))
    """
    pfs = []
    for i in range(dt.num_constructors()):
        cons = dt.constructor(i)
        if cons.arity() > 0:
            xs = [
                smt.FreshConst(cons.domain(j), prefix="x") for j in range(cons.arity())
            ]
            ys = [
                smt.FreshConst(cons.domain(j), prefix="y") for j in range(cons.arity())
            ]
            pfs.append(
                kd.kernel.prove(
                    smt.ForAll(
                        xs + ys,
                        (cons(*xs) == cons(*ys))
                        == smt.And([x == y for x, y in zip(xs, ys)]),
                    )
                )
            )
    return pfs


def recognizer_lemmas(dt: smt.DatatypeSortRef) -> list[kd.kernel.Proof]:
    """

    >>> import kdrag.theories.nat as nat
    >>> recognizer_lemmas(nat.Nat)[0]
    |= is(Z, Z) == True
    """
    pfs = []
    for i in range(dt.num_constructors()):
        recog = dt.recognizer(i)
        for i1 in range(dt.num_constructors()):
            cons = dt.constructor(i1)
            if cons.arity() > 0:
                xs = [
                    smt.FreshConst(cons.domain(j), prefix="x")
                    for j in range(cons.arity())
                ]
                pfs.append(
                    kd.kernel.prove(smt.ForAll(xs, (recog(cons(*xs)) == (i == i1))))
                )
            else:
                pfs.append(kd.kernel.prove(recog(cons()) == (i1 == i)))
    return pfs


def distinct_lemmas(dt: smt.DatatypeSortRef) -> list[kd.kernel.Proof]:
    """
    Constructors are distinct lemmas.

    >>> import kdrag.theories.nat as nat
    >>> distinct_lemmas(nat.Nat)[0]
    |= ForAll(x!..., S(x!...) != Z)
    """
    pfs = []
    for i in range(dt.num_constructors()):
        cons = dt.constructor(i)
        xs = [smt.FreshConst(cons.domain(j), prefix="x") for j in range(cons.arity())]
        for i1 in range(i):
            cons1 = dt.constructor(i1)
            if cons.arity() > 0:
                xs1 = [
                    smt.FreshConst(cons1.domain(j), prefix="y")
                    for j in range(cons1.arity())
                ]
                pfs.append(
                    kd.kernel.prove(smt.ForAll(xs + xs1, cons(*xs) != cons1(*xs1)))
                )
            else:
                pfs.append(kd.kernel.prove(cons() != cons1()))
    return pfs


def accessor_lemmas(dt: smt.DatatypeSortRef) -> list[kd.kernel.Proof]:
    """
    Accessor lemmas for a datatype.

    >>> import kdrag.theories.nat as nat
    >>> accessor_lemmas(nat.Nat)[0]
    |= ForAll(x!..., pred(S(x!...)) == x!...)
    """
    pfs = []
    for i in range(dt.num_constructors()):
        cons = dt.constructor(i)
        xs = [smt.FreshConst(cons.domain(k), prefix="x") for k in range(cons.arity())]
        for j in range(cons.arity()):
            acc = dt.accessor(i, j)
            pfs.append(kd.kernel.prove(smt.ForAll(xs, acc(cons(*xs)) == xs[j])))
    return pfs
