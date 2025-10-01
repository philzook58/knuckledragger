import kdrag.smt as smt
import kdrag as kd
import functools

type SubSort = smt.QuantifierRef | smt.ArrayRef
type Type = SubSort
# User telescope
"""
User telescope type.

Telescopes are dependent or refined contexts of variables.
They can tag variables with SubSet expressions or formulas that involve the bound variable.
Internally, the are normalized to _Tele, which is a list of (variable, formula) pairs.
"""
type Telescope = list[
    tuple[smt.ExprRef, smt.BoolRef] | tuple[smt.ExprRef, SubSort] | smt.ExprRef
]
# Internal normalized telescope
type _Tele = list[tuple[smt.ExprRef, smt.BoolRef]]


def subsort_domain(T: SubSort) -> smt.SortRef:
    """
    Get the domain sort of a SubSort, which is either an ArrayRef or a QuantifierRef.

    >>> T = smt.Array("T", smt.IntSort(), smt.BoolSort())
    >>> subsort_domain(T)
    Int
    >>> x = smt.Int("x")
    >>> subsort_domain(smt.Lambda([x], x > 0))
    Int
    """
    if isinstance(T, smt.ArrayRef):
        return T.domain()
    elif isinstance(T, smt.QuantifierRef):
        assert T.is_lambda()
        return T.var_sort(0)
    else:
        raise TypeError(f"Unsupported type for subsort: {T}")


def normalize(xs: Telescope) -> _Tele:
    """
    Normalize a telescope to a list of (variable, formula) pairs.

    >>> x, y, z = smt.Ints("x y z")
    >>> normalize([x, y, z])
    [(x, True), (y, True), (z, True)]
    >>> normalize([(x, x > 0), (y, y > x), z])
    [(x, x > 0), (y, y > x), (z, True)]
    >>> normalize([(x, smt.Lambda([x], x > 0)), (y, smt.Lambda([y], y > x)), z])
    [(x, x > 0), (y, y > x), (z, True)]
    """
    res: _Tele = []
    for v in xs:
        if isinstance(v, tuple):
            (v, T) = v
            if T.sort() == smt.BoolSort():
                assert isinstance(T, smt.BoolRef)
                res.append((v, T))
            elif isinstance(T, smt.ArrayRef) or (
                isinstance(T, smt.QuantifierRef) and T.is_lambda()
            ):
                P = T(v)
                assert isinstance(P, smt.BoolRef)
                res.append((v, P))
            else:
                raise TypeError(f"Unsupported type for quantifier: {T}")
        else:
            res.append((v, smt.BoolVal(True)))
    return res


def open_binder(e: smt.BoolRef, n: int = 100000) -> tuple[_Tele, smt.BoolRef]:
    """
    Open a formula in telescope form `forall x, P(x), forall y, Q(y), R`

    >>> x, y = smt.Ints("x y")
    >>> open_binder(TForAll([(x, x > 0), (y, y > 0)], x == y))
    ([(X!..., X!... > 0), (Y!..., Y!... > 0)], X!... == Y!...)
    >>> open_binder(TForAll([(x, x > 0), (y, y > 0)], x == y), n=1)
    ([(X!..., X!... > 0)], ForAll(y, Implies(y > 0, X!... == y)))
    """
    tele = []
    while isinstance(e, smt.QuantifierRef) and n > 0:
        n -= 1
        vs, body = kd.utils.open_binder(e)
        assert len(vs) == 1
        v = vs[0]
        assert smt.is_implies(body)
        e = body.arg(1)
        tele.append((v, body.arg(0)))
    return tele, e


def TForAll(xs: Telescope, P: smt.BoolRef) -> smt.BoolRef:
    """
    Dependent forall quantifier for a telescope of variables.
    Kind of like a proof irrelevant Pi type.

    Subtype / Refinement style usage

    >>> x, y, z = smt.Reals("x y z")
    >>> TForAll([(x, x > 0), (y, y > x)], y > -1)
    ForAll(x, Implies(x > 0, ForAll(y, Implies(y > x, y > -1))))

    "Dependent type" style usage

    >>> Pos = smt.Lambda([x], x > 0)
    >>> GT = lambda x: smt.Lambda([y], y > x)
    >>> TForAll([(x, Pos), (y, GT(x))], y > -1)
    ForAll(x, Implies(x > 0, ForAll(y, Implies(y > x, y > -1))))
    """
    for v in reversed(xs):
        if isinstance(v, tuple):
            (v, T) = v
            if T.sort() == smt.BoolSort():
                P = kd.QForAll([v], T, P)
            elif isinstance(T, smt.ArrayRef) or (
                isinstance(T, smt.QuantifierRef) and T.is_lambda()
            ):
                P = kd.QForAll([v], T(v), P)
            else:
                raise TypeError(f"Unsupported type for quantifier: {T}")
        else:
            P = kd.QForAll([v], P)
    return P


def TExists(xs: Telescope, P: smt.BoolRef) -> smt.BoolRef:
    """
    Dependent exists quantifier for a telescope of variables.
    Kind of like a proof irrelevant Sigma type.

    Subtype / Refinement style usage

    >>> x, y, z = smt.Reals("x y z")
    >>> TExists([(x, x > 0), (y, y > x)], y > -1)
    Exists(x, And(x > 0, Exists(y, And(y > x, y > -1))))

    "Dependent type" style usage

    >>> Pos = smt.Lambda([x], x > 0)
    >>> GT = lambda x: smt.Lambda([y], y > x)
    >>> TExists([(x, Pos), (y, GT(x))], y > -1)
    Exists(x, And(x > 0, Exists(y, And(y > x, y > -1))))
    """
    for v in reversed(xs):
        if isinstance(v, tuple):
            (v, T) = v
            if T.sort() == smt.BoolSort():
                P = kd.QExists([v], T, P)
            elif isinstance(T, smt.ArrayRef) or (
                isinstance(T, smt.QuantifierRef) and T.is_lambda()
            ):
                P = kd.QExists([v], T(v), P)
            else:
                raise TypeError(f"Unsupported type for quantifier: {T}")
        else:
            P = kd.QExists([v], P)
    return P


_tsig: dict[smt.FuncDeclRef, kd.Proof] = {}


def axiom_sig(f: smt.FuncDeclRef, tele0: Telescope, T: SubSort) -> kd.Proof:
    """
    Assign signature to a function `f` with a telescope of arguments `tele0` as an axiom

    """
    tele = normalize(tele0)
    vs = [v for v, _ in tele]
    ctx = [P for _, P in tele]
    # T is nonempty when context is possible
    # Otherwise even allowing this declaration is inconsistent
    x = smt.FreshConst(f.range())
    kd.prove(smt.ForAll(vs, smt.Implies(smt.And(ctx), smt.Exists([x], T[x]))))
    pf = kd.axiom(smt.ForAll(vs, smt.Implies(smt.And(ctx), T[f(*vs)])))
    if f in _tsig:
        print("Warning: Redefining function signature", f)
    _tsig[f] = pf
    return pf


def prove_sig(f: smt.FuncDeclRef, tele0: Telescope, T: SubSort, by=None) -> kd.Proof:
    vs = [v for v, _ in normalize(tele0)]
    P = has_type(tele0, f(*vs), T, by=by).forall(vs)
    if f in _tsig:
        print("Warning: Redefining function signature", f)
    _tsig[f] = P
    f.pre_post = P  # type: ignore
    return P


def DeclareFunction(name, tele0: Telescope, T: SubSort, by=[]) -> smt.FuncDeclRef:
    """

    >>> x, y = smt.Ints("x y")
    >>> Nat = smt.Lambda([x], x >= 0)
    >>> GE = lambda x: smt.Lambda([y], y >= x)
    >>> inc = DeclareFunction("inc", [(x, Nat)], GE(x))
    """
    tele = normalize(tele0)
    res_sort = subsort_domain(T)
    f = smt.Function(name, *[v.sort() for v, _ in tele], res_sort)
    P = axiom_sig(f, tele0, T)
    f.pre_post = P
    return f


def HasType(ctx: Telescope, t0: smt.ExprRef, T: SubSort) -> smt.BoolRef:
    """
    Formula that corresponds to typing judgement `ctx |= t0 : T`

    >>> x = smt.Int("x")
    >>> HasType([(x, Nat)], x+1, Pos)
    Implies(And(x >= 0), Lambda(n, n > 0)[x + 1])
    """
    tele = normalize(ctx)
    pctx = [P for _, P in tele]
    return smt.Implies(smt.And(pctx), T[t0])


def has_type(
    ctx: Telescope, t0: smt.ExprRef, T: SubSort, by=None, **kwargs
) -> kd.Proof:
    """
    Tactic to check that an expression `t0` has type `T` in a context `ctx`.

    >>> x = smt.Int("x")
    >>> Nat = smt.Lambda([x], x >= 0)
    >>> has_type([(x, Nat)], x+1, Nat)
    |= Implies(And(x >= 0), Lambda(x, x >= 0)[x + 1])
    """
    if by is None:
        by = []
    seen = set()
    todo = [t0]
    while todo:
        t = todo.pop()
        if smt.is_app(t):
            children = t.children()
            decl = t.decl()
            for c in children:
                if c not in seen:
                    todo.append(c)
                    seen.add(c)
            # TODO. Could recursively cut the children. Localize type error better.
            if decl.name() == "ann":
                try:
                    x, T = children
                    by.append(has_type(ctx, x, T, by=by))
                    # TODO: unfold ann. by.append(kd.kernel.defn)
                    # actually with new definition, ann is in _tsig
                except Exception as e:
                    raise TypeError(f"Invalid annotation {t} in context {ctx}", e)
            if decl in _tsig:
                by.append(_tsig[decl](*children))

    return kd.prove(HasType(ctx, t0, T), by=by, **kwargs)


def define(
    name: str, args: Telescope, T: SubSort, body: smt.ExprRef, by=None, **kwargs
) -> smt.FuncDeclRef:
    """
    Define a function with a precondition given by a telescope of arguments
    and a postcondition given by a subset that output will lie in.

    Automatically

    >>> n = kd.kernel.FreshVar("n", smt.IntSort())
    >>> m = smt.Int("m")
    >>> inc = define("test_inc", [(n,Nat)], Pos, n + 1)
    >>> inc.pre_post
    |= ForAll(n!...,
        Implies(And(n!... >= 0),
            Lambda(n, n > 0)[test_inc(n!...)]))
    >>> pred = define("pred", [(n, Pos)], Nat, n - 1)
    >>> myid = define("myid", [(n, Nat)], Nat, pred(inc(n)))
    """
    P1 = has_type(args, body, T, by=by, **kwargs)
    tele = normalize(args)
    vs = [v for (v, _) in tele]
    for v in vs:
        if not kd.kernel.is_fresh_var(v):
            raise TypeError(f"Arguments must be schema variables: {v}")
    f = kd.define(name, vs, body)
    prove_sig(f, args, T, by=[P1, f.defn(*vs)])
    return f


def Program(name: str, args: Telescope, T: SubSort, body: smt.ExprRef):
    return ProgramState(name, args, T, body)


class ProgramState(kd.tactics.ProofState):
    """
    Interactive proof of a function definition.
    See https://rocq-prover.org/doc/master/refman/addendum/program.html

    >>> n = kd.kernel.FreshVar("n", smt.IntSort())
    >>> m = smt.Int("m")
    >>> l = Program("test_inc1", [(n,Nat)], Pos, n + 1)
    >>> l.define()
    test_inc1
    """

    def __init__(self, name: str, args: Telescope, T: SubSort, body: smt.ExprRef):
        self.name = name
        self.args = args
        self.T = T
        self.body = body
        # TODO: start with args in the sig
        super().__init__(kd.tactics.Goal(sig=[], ctx=[], goal=HasType(args, body, T)))

    def define(self):
        # TODO: we prove twice?
        return define(self.name, self.args, self.T, self.body, by=[self.qed()])


@functools.lru_cache(maxsize=None)
def _gen_annotate(S: smt.SortRef):
    x, y = kd.tactics.FreshVars("x y", S)
    T = kd.kernel.FreshVar("T", smt.ArraySort(S, smt.BoolSort()))
    assert isinstance(T, smt.ArrayRef)
    return define(
        "ann",
        [(x, T), T],  # This is breaking telescoping rules. Is that ok?
        smt.Lambda([y], y == x),
        smt.If(T[x], x, smt.FreshFunction(S, S)(x)),
    )


def ann(x: smt.ExprRef, T: SubSort) -> smt.ExprRef:
    """
    Annotate an expression with a type.

    >>> x = smt.Int("x")
    >>> ann(x, Nat)
    ann(x, Lambda(n, n >= 0))
    """
    return _gen_annotate(x.sort())(x, T)


# For Proof objects
Unit = kd.Inductive("Unit")
Unit.declare("tt")
Unit = Unit.create()

_n = smt.Int("n")
Nat = smt.Lambda([_n], _n >= 0)
Pos = smt.Lambda([_n], _n > 0)


# type Family = Callable[..., SubSort]
def Fin(n):
    """
    >>> m = smt.Int("m")
    >>> Fin(3)
    Lambda(x, And(Lambda(n, n >= 0)[x], x < 3))
    >>> kd.prove(smt.Not(smt.Exists([m], Fin(0)[m])))
    |= Not(Exists(m,
            Lambda(x, And(Lambda(n, n >= 0)[x], x < 0))[m]))
    """
    x = smt.Int("x")
    return smt.Lambda([x], smt.And(Nat[x], x < n))


_x = smt.Real("x")
Interval = smt.Lambda([_x], smt.And(0 <= _x, _x <= 1))


def Pi(tele0: Telescope, B: SubSort) -> SubSort:
    """
    Multiarity Pi. Dependent Function subsort
    B is a family because it may include parameters from tele0.

    >>> x, y = smt.Ints("x y")
    >>> GE = lambda x: smt.Lambda([y], y >= x)
    >>> Pi([(x, Nat)], GE(x))
    Lambda(f!...,
        ForAll(x, Implies(x >= 0, Lambda(y, y >= x)[f!...[x]])))
    >>> smt.simplify(Pi([(x, Nat)], GE(x))[smt.Lambda([x], x)])
    True
    """
    tele = normalize(tele0)
    vs = [v for v, _ in tele]
    # TB: SubSort = B(*vs)  # B is a family of sorts
    sorts = [v.sort() for (v, _) in tele]
    fsort = smt.ArraySort(*sorts, subsort_domain(B))
    f = smt.FreshConst(fsort, prefix="f")
    return smt.Lambda([f], TForAll(tele0, B[f(*vs)]))


def Id(x: smt.ExprRef, y: smt.ExprRef) -> SubSort:
    """
    >>> x, y = smt.Ints("x y")
    >>> p = smt.Const("p", Unit)
    >>> has_type([x], Unit.tt, Id(x, x))
    |= Implies(And(True), Lambda(p!..., x == x)[tt])
    >>> has_type([x, y, (p, Id(x,y))], Unit.tt, Id(y, x))
    |= Implies(And(True, True, x == y), Lambda(p!..., y == x)[tt])
    """
    p = smt.FreshConst(Unit, prefix="p")
    return smt.Lambda([p], x == y)
