"""
The transfinite recursion theorem (Halmos §18).

W is well ordered by R, and F is a sequence function of type W in X: it sends
each function t from an initial segment s(a) into X to an element F t of X.
Then U = trec(R, W, X, F) is a function from W into X with U(a) = F(U^a), where
U^a is the restriction of U to s(a). As in Halmos, U is the smallest f-closed
subset of W × X, and the proof reuses the diminished-set argument of the
recursion theorem on ω. No Replacement is needed.
"""

from kdrag import Theorem, define, prove
from kdrag.smt import (
    And,
    ArraySort,
    BoolSort,
    Consts,
    Exists,
    ForAll,
    Implies,
    Lambda,
    Not,
)
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import ZFSet, elem, le, pair, pow, prod, sep, sing
from kdrag.contrib.zf.fun import (
    app,
    app_eq_of_pair_elem,
    elem_sinter,
    elem_sub,
    is_func,
    pair_elem_prod,
    sinter,
)
from kdrag.contrib.zf.poset import is_well_order, seg, well_order_induction

A, S, W, X, a, b, p, t, x, y, z = Consts("A S W X a b p t x y z", ZFSet)
R = Consts("R", ArraySort(ZFSet, ZFSet, BoolSort()))[0]
F = Consts("F", ArraySort(ZFSet, ZFSet))[0]

# Halmos' U^a: the restriction of a relation to a set of first coordinates.
restrict = define(
    "restrict",
    [A, S],
    sep(A, Lambda(p, Exists([x, y], And(elem(x, S), p == pair(x, y))))),
)

# F is a sequence function of type W in X.
is_seq_fn = define(
    "is_seq_fn",
    [F, R, W, X],
    ForAll([a, t], elem(a, W), is_func(t, seg(R, W, a), X), elem(F[t], X)),
)

# Halmos: A is f-closed when (a, F t) ∈ A for every function t ⊆ A from s(a) into X.
trec_closed = define(
    "trec_closed",
    [A, F, R, W, X],
    ForAll(
        [a, t], elem(a, W), is_func(t, seg(R, W, a), X), t <= A, elem(pair(a, F[t]), A)
    ),
)
trec = define(
    "trec",
    [F, R, W, X],
    sinter(sep(pow(prod(W, X)), Lambda(A, trec_closed(A, F, R, W, X)))),
)


def _hyps(F, R, W, X):
    return [is_well_order(R, W), is_seq_fn(F, R, W, X)]


@Theorem(ForAll([F, R, W, X], *_hyps(F, R, W, X), trec_closed(prod(W, X), F, R, W, X)))
def trec_closed_prod(l):
    """W × X is f-closed, so the family defining U is nonempty."""
    F, R, W, X = l.fixes()
    l.intros()
    l.unfold(trec_closed)
    a0, t0 = l.fixes()
    l.intros()
    l.auto(by=[pair_elem_prod, is_seq_fn.defn(F, R, W, X)])


@Theorem(
    ForAll(
        [F, R, W, X, p],
        *_hyps(F, R, W, X),
        elem(p, trec(F, R, W, X))
        == ForAll(A, A <= prod(W, X), trec_closed(A, F, R, W, X), elem(p, A)),
    )
)
def elem_trec(l):
    F, R, W, X, p = l.fixes()
    l.intros()
    l.unfold(trec)
    fam = sep(pow(prod(W, X)), Lambda(A, trec_closed(A, F, R, W, X)))
    l.have(
        elem(prod(W, X), fam),
        by=[zf.elem_sep, zf.elem_pow, le.defn, trec_closed_prod(F, R, W, X)],
    )
    l.have(fam != zf.emp, by=[zf.elem_emp])
    l.auto(by=[elem_sinter(fam, p), zf.elem_sep, zf.elem_pow])


@Theorem(
    ForAll(
        [F, R, W, X, A],
        *_hyps(F, R, W, X),
        A <= prod(W, X),
        trec_closed(A, F, R, W, X),
        trec(F, R, W, X) <= A,
    )
)
def trec_le_of_closed(l):
    """U is the smallest f-closed set."""
    F, R, W, X, A = l.fixes()
    l.intros()
    l.unfold(le)
    p0 = l.fix()
    l.auto(by=[elem_trec(F, R, W, X, p0)])


trec_le_prod = prove(
    ForAll([F, R, W, X], *_hyps(F, R, W, X), trec(F, R, W, X) <= prod(W, X)),
    by=[trec_le_of_closed, trec_closed_prod, le.defn],
)


@Theorem(
    ForAll([F, R, W, X], *_hyps(F, R, W, X), trec_closed(trec(F, R, W, X), F, R, W, X))
)
def trec_closed_trec(l):
    """U is f-closed: a function t ⊆ U lies inside every f-closed A."""
    F, R, W, X = l.fixes()
    U = trec(F, R, W, X)
    l.intros()
    l.unfold(trec_closed)
    a0, t0 = l.fixes()
    l.intros()
    q = pair(a0, F[t0])
    l.have(ForAll(A, A <= prod(W, X), trec_closed(A, F, R, W, X), elem(q, A)))
    A0 = l.fix()
    l.intros()
    l.have(U <= A0, by=[trec_le_of_closed(F, R, W, X, A0)])
    l.have(t0 <= A0, by=[le.defn(t0, U), le.defn(U, A0), le.defn(t0, A0)])
    l.auto(by=[trec_closed.defn(A0, F, R, W, X)])
    l.auto(by=[elem_trec(F, R, W, X, q)])


@Theorem(
    ForAll(
        [F, R, W, X, p],
        *_hyps(F, R, W, X),
        trec_closed(trec(F, R, W, X) - sing(p), F, R, W, X),
        Not(elem(p, trec(F, R, W, X))),
    )
)
def not_elem_trec_of_sub_sing(l):
    """Halmos' diminished set: if U - {p} is still f-closed, p was never in U."""
    F, R, W, X, p = l.fixes()
    U = trec(F, R, W, X)
    l.intros()
    l.intro()
    l.have(U - sing(p) <= prod(W, X), by=[trec_le_prod(F, R, W, X), le.defn, elem_sub])
    l.have(U <= U - sing(p), by=[trec_le_of_closed(F, R, W, X, U - sing(p))])
    l.auto(by=[le.defn(U, U - sing(p)), elem_sub, zf.elem_sing])


# Restrictions and functions inside U

T1, T2 = Consts("T1 T2", ZFSet)

elem_restrict_pair = prove(
    ForAll(
        [A, S, x, y],
        elem(pair(x, y), restrict(A, S)) == And(elem(pair(x, y), A), elem(x, S)),
    ),
    by=[restrict.defn, zf.elem_sep, zf.pair_inj],
)
restrict_le = prove(
    ForAll([A, S], restrict(A, S) <= A), by=[restrict.defn, zf.elem_sep, le.defn]
)


@Theorem(
    ForAll(
        [T1, T2, A, S, X],
        is_func(T1, S, X),
        is_func(T2, S, X),
        T1 <= A,
        T2 <= A,
        ForAll([x, y, z], elem(x, S), elem(pair(x, y), A), elem(pair(x, z), A), y == z),
        T1 == T2,
    )
)
def func_eq_of_le(l):
    """Two functions on S inside A agree when A has at most one value at each x ∈ S."""
    T1, T2, A, S, X = l.fixes()
    l.intros()
    l.rw(zf.ext_ax)
    p0 = l.fix()
    # Each p in either function is (x, y) with x ∈ S, and the other function's value
    # at x lies in A too, so it is y.
    l.have(
        ForAll(
            T1,
            is_func(T1, S, X),
            elem(p0, T1),
            Exists([x, y], And(elem(x, S), p0 == pair(x, y))),
        ),
        by=[is_func.defn, le.defn, zf.elem_prod_def],
    )
    l.auto(by=[is_func.defn(T1, S, X), is_func.defn(T2, S, X), le.defn])


def unique_value(u, a):
    """There is exactly one x with (a, x) ∈ u."""
    return Exists(x, And(elem(pair(a, x), u), ForAll(y, elem(pair(a, y), u), y == x)))


@Theorem(
    ForAll(
        [F, R, W, X],
        *_hyps(F, R, W, X),
        ForAll(
            a,
            elem(a, W),
            ForAll(b, elem(b, seg(R, W, a)), unique_value(trec(F, R, W, X), b)),
            unique_value(trec(F, R, W, X), a),
        ),
    )
)
def trec_unique_value_step(l):
    """Halmos: if every b < a has a unique value, so does a, namely F(U^a)."""
    F, R, W, X = l.fixes()
    U = trec(F, R, W, X)
    l.intros()
    a0 = l.fix()
    l.intros()
    sa = seg(R, W, a0)
    T = restrict(U, sa)
    # By hypothesis U has at most one value at each b < a.
    l.have(
        ForAll([x, y, z], elem(x, sa), elem(pair(x, y), U), elem(pair(x, z), U), y == z)
    )
    x0, y0, z0 = l.fixes()
    l.intros()
    l.auto()
    # U^a is a function from s(a) into X inside U ...
    l.have(T <= U, by=[restrict_le(U, sa)])
    l.have(is_func(T, sa, X))
    l.unfold(is_func)
    l.split()
    l.unfold(le)
    l.fix()
    l.intro()
    l.auto(
        by=[
            restrict.defn(U, sa),
            zf.elem_sep,
            trec_le_prod(F, R, W, X),
            le.defn,
            pair_elem_prod,
            zf.pair_inj,
        ]
    )
    l.fix()
    l.intro()
    l.auto(by=[elem_restrict_pair])
    x2, y2, z2 = l.fixes()
    l.intros()
    l.auto(by=[elem_restrict_pair])
    # ... so (a, F(U^a)) ∈ U, since U is f-closed.
    l.have(
        elem(pair(a0, F[T]), U),
        by=[trec_closed_trec(F, R, W, X), trec_closed.defn(U, F, R, W, X)],
    )
    l.exists(F[T])
    l.split()
    l.auto()
    # If (a, c) ∈ U with c ≠ F(U^a), the diminished set U - {(a, c)} is f-closed:
    # a step onto (a, c) would use some t ⊆ U on s(a), which must be U^a.
    c = l.fix()
    l.intro()
    l.contra()
    p1 = pair(a0, c)
    l.have(trec_closed(U - sing(p1), F, R, W, X))
    l.unfold(trec_closed)
    b0, t0 = l.fixes()
    l.intros()
    l.have(t0 <= U, by=[le.defn, elem_sub])
    l.have(
        elem(pair(b0, F[t0]), U),
        by=[trec_closed_trec(F, R, W, X), trec_closed.defn(U, F, R, W, X)],
    )
    l.have(Implies(b0 == a0, t0 == T), by=[func_eq_of_le(t0, T, U, sa, X)])
    l.auto(by=[elem_sub, zf.elem_sing, zf.pair_inj])
    l.auto(by=[not_elem_trec_of_sub_sing(F, R, W, X, p1)])


@Theorem(
    ForAll(
        [F, R, W, X],
        *_hyps(F, R, W, X),
        ForAll(a, elem(a, W), unique_value(trec(F, R, W, X), a)),
    )
)
def trec_unique_value(l):
    """By transfinite induction, U has exactly one value at each a ∈ W."""
    F, R, W, X = l.fixes()
    U = trec(F, R, W, X)
    l.intros()
    ind = well_order_induction(R, W, Lambda(a, unique_value(U, a)))
    l.auto(by=[ind, trec_unique_value_step(F, R, W, X)])


@Theorem(ForAll([F, R, W, X], *_hyps(F, R, W, X), is_func(trec(F, R, W, X), W, X)))
def trec_is_func(l):
    F, R, W, X = l.fixes()
    U = trec(F, R, W, X)
    l.intros()
    l.unfold(is_func)
    l.have(U <= prod(W, X), by=[trec_le_prod(F, R, W, X)])
    # Totality and single-valuedness both come from the unique value at each a ∈ W.
    l.auto(by=[trec_unique_value(F, R, W, X), le.defn(U, prod(W, X)), pair_elem_prod])


@Theorem(
    ForAll(
        [F, R, W, X, a],
        *_hyps(F, R, W, X),
        elem(a, W),
        app(trec(F, R, W, X), a) == F[restrict(trec(F, R, W, X), seg(R, W, a))],
    )
)
def trec_eq(l):
    """Halmos' transfinite recursion theorem: U(a) = f(U^a) for each a ∈ W."""
    F, R, W, X, a0 = l.fixes()
    U = trec(F, R, W, X)
    l.intros()
    l.have(is_func(U, W, X), by=[trec_is_func(F, R, W, X)])
    # U^a is a function from s(a) into X inside U, so (a, F(U^a)) ∈ U.
    T = restrict(U, seg(R, W, a0))
    l.have(T <= U, by=[restrict_le])
    l.have(
        is_func(T, seg(R, W, a0), X),
        by=[
            is_func.defn(U, W, X),
            is_func.defn(T, seg(R, W, a0), X),
            elem_restrict_pair,
            restrict.defn(U, seg(R, W, a0)),
            zf.elem_sep,
            le.defn,
            pair_elem_prod,
            seg.defn(R, W, a0),
        ],
    )
    l.have(
        elem(pair(a0, F[T]), U),
        by=[trec_closed_trec(F, R, W, X), trec_closed.defn(U, F, R, W, X)],
    )
    l.auto(by=[app_eq_of_pair_elem(U, W, X, a0, F[T])])
