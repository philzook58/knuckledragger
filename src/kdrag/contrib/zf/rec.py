"""
The recursion theorem on ω (Halmos §12).

Given `a ∈ X` and a step `F` mapping X into X, `nat_rec(X, a, F)` is the
smallest set of pairs containing `(0, a)` and closed under
`(n, x) ↦ (n⁺, F x)`. It is a function from ω to X with
`u(0) = a` and `u(n⁺) = F(u(n))`. The step is an ordinary HOL function
`ZFSet → ZFSet`; Halmos' set-function version is the case `F = app(f, ·)`.
"""

from kdrag import Theorem, define, prove
from kdrag.smt import And, ArraySort, Const, Consts, Exists, ForAll, Lambda, Not
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import (
    ZFSet,
    biginter,
    elem,
    emp,
    le,
    pair,
    pow,
    prod,
    sep,
    sing,
    succ,
    zero,
)
from kdrag.contrib.zf.nat import (
    induct_omega,
    omega,
    omega_succ,
    omega_zero,
    succ_inj,
    succ_ne_zero,
)
from kdrag.contrib.zf.fun import (
    app,
    app_eq_of_pair_elem,
    elem_sub,
    is_func,
    pair_app_elem,
    pair_elem_prod,
)

A, X, a, n, m, p, t, x, y = Consts("A X a n m p t x y", ZFSet)
F = Const("F", ArraySort(ZFSet, ZFSet))

maps_to = define("maps_to", [F, X], ForAll(x, elem(x, X), elem(F[x], X)))

rec_closed = define(
    "rec_closed",
    [A, a, F],
    And(
        elem(pair(zero, a), A),
        ForAll([n, x], elem(pair(n, x), A), elem(pair(succ(n), F[x]), A)),
    ),
)

# Halmos' 𝒞: the closed subsets of ω × X. Its intersection is the recursive function.
rec_family = define(
    "rec_family",
    [X, a, F],
    sep(pow(prod(omega, X)), Lambda(A, rec_closed(A, a, F))),
)
nat_rec = define("nat_rec", [X, a, F], biginter(rec_family(X, a, F)))


@Theorem(
    ForAll(
        [A, X, a, F],
        elem(A, rec_family(X, a, F)) == And(A <= prod(omega, X), rec_closed(A, a, F)),
    )
)
def elem_rec_family(l):
    A, X, a, F = l.fixes()
    l.unfold(rec_family)
    l.rw(zf.elem_sep)
    l.rw(zf.elem_pow)
    l.auto()


@Theorem(ForAll([X, a, F], elem(a, X), maps_to(F, X), rec_closed(prod(omega, X), a, F)))
def rec_closed_prod(l):
    """ω × X itself is closed, so 𝒞 is nonempty."""
    X, a, F = l.fixes()
    l.intros()
    l.unfold(rec_closed)
    l.auto(by=[pair_elem_prod, omega_zero, omega_succ, maps_to.defn(F, X)])


prod_elem_rec_family = prove(
    ForAll(
        [X, a, F], elem(a, X), maps_to(F, X), elem(prod(omega, X), rec_family(X, a, F))
    ),
    by=[elem_rec_family, rec_closed_prod, le.defn],
)


@Theorem(
    ForAll(
        [X, a, F, x],
        elem(a, X),
        maps_to(F, X),
        elem(x, nat_rec(X, a, F))
        == ForAll(A, elem(A, rec_family(X, a, F)), elem(x, A)),
    )
)
def elem_nat_rec(l):
    X, a, F, x = l.fixes()
    l.intros()
    l.unfold(nat_rec)
    # 𝒞 is nonempty, so ⋂𝒞 has the expected members.
    l.have(rec_family(X, a, F) != emp, by=[prod_elem_rec_family(X, a, F), zf.elem_emp])
    l.auto(by=[zf.elem_biginter])


@Theorem(
    ForAll(
        [X, a, F, A],
        elem(a, X),
        maps_to(F, X),
        A <= prod(omega, X),
        rec_closed(A, a, F),
        nat_rec(X, a, F) <= A,
    )
)
def nat_rec_le_of_closed(l):
    """nat_rec is below every closed set: it is the smallest one."""
    X, a, F, A = l.fixes()
    l.intros()
    l.unfold(le)
    p = l.fix()
    l.auto(by=[elem_nat_rec(X, a, F, p), elem_rec_family(A, X, a, F)])


nat_rec_le_prod = prove(
    ForAll([X, a, F], elem(a, X), maps_to(F, X), nat_rec(X, a, F) <= prod(omega, X)),
    by=[nat_rec_le_of_closed, rec_closed_prod, le.defn],
)


@Theorem(
    ForAll([X, a, F], elem(a, X), maps_to(F, X), rec_closed(nat_rec(X, a, F), a, F))
)
def nat_rec_closed(l):
    """nat_rec is closed: every closed set contains (0, a) and is closed under the step."""
    X, a, F = l.fixes()
    l.intros()
    l.unfold(rec_closed)
    l.split()
    l.auto(by=[elem_nat_rec, elem_rec_family, rec_closed.defn])
    l.fixes()
    l.auto(by=[elem_nat_rec, elem_rec_family, rec_closed.defn])


@Theorem(
    ForAll(
        [A, a, F, p],
        rec_closed(A, a, F),
        pair(zero, a) != p,
        ForAll([n, x], elem(pair(n, x), A - sing(p)), pair(succ(n), F[x]) != p),
        rec_closed(A - sing(p), a, F),
    )
)
def rec_closed_sub_sing(l):
    """Removing a pair p keeps a set closed unless p is (0, a) or a step lands on p."""
    A, a, F, p = l.fixes()
    l.intros()
    l.unfold(rec_closed)
    l.auto(by=[rec_closed.defn(A, a, F), elem_sub, zf.elem_sing])


@Theorem(
    ForAll(
        [X, a, F, p],
        elem(a, X),
        maps_to(F, X),
        elem(p, nat_rec(X, a, F)),
        Not(rec_closed(nat_rec(X, a, F) - sing(p), a, F)),
    )
)
def not_rec_closed_nat_rec_sub_sing(l):
    """No pair can be removed from nat_rec: the result would be a smaller closed set."""
    X, a, F, p = l.fixes()
    u = nat_rec(X, a, F)
    l.intros()
    l.intro()
    l.have(
        u - sing(p) <= prod(omega, X), by=[nat_rec_le_prod(X, a, F), le.defn, elem_sub]
    )
    l.have(u <= u - sing(p), by=[nat_rec_le_of_closed(X, a, F, u - sing(p))])
    # But p ∈ u and p ∉ u - {p}.
    l.auto(by=[le.defn(u, u - sing(p)), elem_sub, zf.elem_sing])


def unique_value(u, n):
    """There is exactly one x with (n, x) ∈ u."""
    return Exists(x, And(elem(pair(n, x), u), ForAll(y, elem(pair(n, y), u), y == x)))


@Theorem(
    ForAll(
        [X, a, F],
        elem(a, X),
        maps_to(F, X),
        ForAll(n, elem(n, omega), unique_value(nat_rec(X, a, F), n)),
    )
)
def nat_rec_unique_value(l):
    """Halmos: by induction on n, nat_rec has exactly one value at each n ∈ ω."""
    X, a, F = l.fixes()
    u = nat_rec(X, a, F)
    l.intros()
    n = l.fix()
    l.intro()
    l.induct(n, using=induct_omega)

    # Base case: the value at 0 is a.
    l.exists(a)
    l.split()
    l.auto(by=[nat_rec_closed(X, a, F), rec_closed.defn])
    b = l.fix()
    l.intro()
    l.contra()
    # If also (0, b) ∈ u with b ≠ a, then u - {(0, b)} is still closed:
    # it keeps (0, a), and no step lands on 0.
    p0 = pair(zero, b)
    l.have(pair(zero, a) != p0, by=[zf.pair_inj])
    l.have(
        ForAll([m, t], elem(pair(m, t), u - sing(p0)), pair(succ(m), F[t]) != p0),
        by=[zf.pair_inj, succ_ne_zero],
    )
    l.have(
        rec_closed(u - sing(p0), a, F),
        by=[rec_closed_sub_sing(u, a, F, p0), nat_rec_closed(X, a, F)],
    )
    l.auto(by=[not_rec_closed_nat_rec_sub_sing(X, a, F, p0)])

    # Inductive step: if x is the unique value at k, then F x is the unique value at k⁺.
    k = l.fix()
    _, ih = l.intros()
    x0, _ = l.obtain(ih)
    l.exists(F[x0])
    l.split()
    l.auto(by=[nat_rec_closed(X, a, F), rec_closed.defn])
    c = l.fix()
    l.intro()
    l.contra()
    # If also (k⁺, c) ∈ u with c ≠ F x, remove (k⁺, c). It is not (0, a) since k⁺ ≠ 0.
    p1 = pair(succ(k), c)
    l.have(pair(zero, a) != p1, by=[zf.pair_inj, succ_ne_zero])
    # A step (m, t) ↦ (m⁺, F t) landing on (k⁺, c) forces m = k by Peano V,
    # then t = x by uniqueness at k, so c = F x: a contradiction.
    l.have(ForAll([m, t], elem(pair(m, t), u - sing(p1)), pair(succ(m), F[t]) != p1))
    m1, t1 = l.fixes()
    l.intro()
    l.contra()
    l.have(
        elem(m1, omega),
        by=[nat_rec_le_prod(X, a, F), le.defn, elem_sub, pair_elem_prod],
    )
    l.have(And(succ(m1) == succ(k), F[t1] == c), by=[zf.pair_inj])
    l.have(m1 == k, by=[succ_inj(m1, k)])
    l.auto(by=[elem_sub])
    l.have(
        rec_closed(u - sing(p1), a, F),
        by=[rec_closed_sub_sing(u, a, F, p1), nat_rec_closed(X, a, F)],
    )
    l.auto(by=[not_rec_closed_nat_rec_sub_sing(X, a, F, p1)])


@Theorem(
    ForAll([X, a, F], elem(a, X), maps_to(F, X), is_func(nat_rec(X, a, F), omega, X))
)
def nat_rec_is_func(l):
    X, a, F = l.fixes()
    u = nat_rec(X, a, F)
    l.intros()
    l.unfold(is_func)
    l.have(u <= prod(omega, X), by=[nat_rec_le_prod(X, a, F)])
    huniq = nat_rec_unique_value(X, a, F)
    # Totality and single-valuedness both come from the unique value at each n ∈ ω.
    l.auto(by=[huniq, le.defn(u, prod(omega, X)), pair_elem_prod])


nat_rec_zero = prove(
    ForAll([X, a, F], elem(a, X), maps_to(F, X), app(nat_rec(X, a, F), zero) == a),
    by=[
        app_eq_of_pair_elem,
        nat_rec_is_func,
        nat_rec_closed,
        rec_closed.defn,
    ],
)


@Theorem(
    ForAll(
        [X, a, F, n],
        elem(a, X),
        maps_to(F, X),
        elem(n, omega),
        app(nat_rec(X, a, F), succ(n)) == F[app(nat_rec(X, a, F), n)],
    )
)
def nat_rec_succ(l):
    X, a, F, n = l.fixes()
    u = nat_rec(X, a, F)
    l.intros()
    l.have(is_func(u, omega, X), by=[nat_rec_is_func(X, a, F)])
    # (n, u(n)) ∈ u, so closure puts (n⁺, F(u(n))) ∈ u.
    l.have(elem(pair(n, app(u, n)), u), by=[pair_app_elem(u, omega, X, n)])
    l.have(
        elem(pair(succ(n), F[app(u, n)]), u),
        by=[nat_rec_closed(X, a, F), rec_closed.defn(u, a, F)],
    )
    l.auto(by=[app_eq_of_pair_elem(u, omega, X, succ(n), F[app(u, n)])])
