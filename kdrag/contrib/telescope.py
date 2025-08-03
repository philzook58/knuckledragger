import kdrag.smt as smt
import kdrag as kd

type SubSort = smt.QuantifierRef | smt.ArrayRef
type Type = SubSort
# User telescope
type Telescope = list[
    tuple[smt.ExprRef, smt.BoolRef] | tuple[smt.ExprRef, SubSort] | smt.ExprRef
]
# Internal normalized telescope
type _Tele = list[tuple[smt.ExprRef, smt.BoolRef]]


def subsort_domain(T: SubSort) -> smt.SortRef:
    """
    Get the domain sort of a SubSort, which is either an ArrayRef or a QuantifierRef.
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
    vs = [v for v, _ in tele]
    ctx = [P for _, P in tele]
    # T is nonempty when context is possible
    # Otherwise even allowing this declaration is inconsistent
    x = smt.FreshConst(res_sort)
    kd.prove(smt.ForAll(vs, smt.Implies(smt.And(ctx), smt.Exists([x], T[x]))), by=by)
    P = kd.axiom(smt.ForAll(vs, smt.Implies(smt.And(ctx), T[f(*vs)])))
    f.pre_post = P
    if f in _tsig:
        print("Warning: Redefining function", f)
    _tsig[f] = P
    return f


def has_type(ctx: Telescope, t0: smt.ExprRef, T: SubSort, by=None) -> kd.Proof:
    tele = normalize(ctx)
    pctx = [P for _, P in tele]
    if by is None:
        by = []
    seen = set()
    todo = [t0]
    while todo:
        t = todo.pop()
        if t in seen:
            continue
        elif smt.is_app(t):
            children = t.children()
            todo.extend(children)
            seen.union(children)
            decl = t.decl()
            if decl in _tsig:
                by.append(_tsig[decl](*children))
    return kd.prove(smt.Implies(smt.And(pctx), T[t0]), by=by)


def define(
    name: str, args: Telescope, T: SubSort, body: smt.ExprRef, by=None
) -> smt.FuncDeclRef:
    """
    Define a function with a precondition given by a telescope of arguments
    and a postcondition given by a subset that output will lie in.

    Automatically

    >>> n = kd.kernel.SchemaVar("n", smt.IntSort())
    >>> m = smt.Int("m")
    >>> Nat = smt.Lambda([n], n >= 0)
    >>> Pos = smt.Lambda([n], n > 0)
    >>> inc = define("inc", [(n,Nat)], Pos, n + 1)
    >>> inc.pre_post
    |= ForAll(n!...,
           Implies(And(n!... >= 0),
                   Lambda(n!..., n!... > 0)[inc(n!...)]))
    >>> pred = define("pred", [(n, Pos)], Nat, n - 1)
    >>> myid = define("myid", [(n, Nat)], Nat, pred(inc(n)))
    """
    P1 = has_type(args, body, T, by=by)
    tele = normalize(args)
    vs = [v for (v, _) in tele]
    ctx = [P for _, P in tele]
    f = kd.define(name, vs, body)
    P2 = smt.Implies(smt.And(ctx), T[f(*vs)])
    P2 = kd.prove(P2, by=[P1, f.defn(*vs)]).forall(vs)
    _tsig[f] = P2
    f.pre_post = P2  # type: ignore
    return f
