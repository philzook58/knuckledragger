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
    maps_to,
    pair_app_elem,
    pair_elem_prod,
)

A, X, a, c, k, n, m, p, t, x, y = Consts("A X a c k n m p t x y", ZFSet)
F = Const("F", ArraySort(ZFSet, ZFSet))

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


@Theorem(
    ForAll([X, a, F], elem(a, X), maps_to(F, X, X), rec_closed(prod(omega, X), a, F))
)
def rec_closed_prod(l):
    """ω × X itself is closed, so 𝒞 is nonempty."""
    X, a, F = l.fixes()
    l.intros()
    l.unfold(rec_closed)
    l.auto(by=[pair_elem_prod, omega_zero, omega_succ, maps_to.defn(F, X, X)])


prod_elem_rec_family = prove(
    ForAll(
        [X, a, F],
        elem(a, X),
        maps_to(F, X, X),
        elem(prod(omega, X), rec_family(X, a, F)),
    ),
    by=[elem_rec_family, rec_closed_prod, le.defn],
)


@Theorem(
    ForAll(
        [X, a, F, x],
        elem(a, X),
        maps_to(F, X, X),
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
        maps_to(F, X, X),
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
    ForAll([X, a, F], elem(a, X), maps_to(F, X, X), nat_rec(X, a, F) <= prod(omega, X)),
    by=[nat_rec_le_of_closed, rec_closed_prod, le.defn],
)


@Theorem(
    ForAll([X, a, F], elem(a, X), maps_to(F, X, X), rec_closed(nat_rec(X, a, F), a, F))
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
        maps_to(F, X, X),
        pair(zero, a) != p,
        ForAll(
            [m, t],
            elem(pair(m, t), nat_rec(X, a, F) - sing(p)),
            pair(succ(m), F[t]) != p,
        ),
        Not(elem(p, nat_rec(X, a, F))),
    )
)
def not_elem_nat_rec_of_sub_sing(l):
    """
    Halmos' diminished set: if u - {p} still contains (0, a) and no step from it
    lands on p, then u - {p} is closed, so p was never in the smallest closed set u.
    """
    X, a, F, p = l.fixes()
    u = nat_rec(X, a, F)
    l.intros()
    l.intro()
    l.have(
        rec_closed(u - sing(p), a, F),
        by=[rec_closed_sub_sing(u, a, F, p), nat_rec_closed(X, a, F)],
    )
    l.have(
        u - sing(p) <= prod(omega, X), by=[nat_rec_le_prod(X, a, F), le.defn, elem_sub]
    )
    l.have(u <= u - sing(p), by=[nat_rec_le_of_closed(X, a, F, u - sing(p))])
    # But p ∈ u and p ∉ u - {p}.
    l.auto(by=[le.defn(u, u - sing(p)), elem_sub, zf.elem_sing])


@Theorem(
    ForAll(
        [X, a, F, k, x, c],
        elem(a, X),
        maps_to(F, X, X),
        elem(k, omega),
        ForAll(y, elem(pair(k, y), nat_rec(X, a, F)), y == x),
        c != F[x],
        ForAll(
            [m, t],
            elem(pair(m, t), nat_rec(X, a, F)),
            pair(succ(m), F[t]) != pair(succ(k), c),
        ),
    )
)
def nat_rec_step_ne(l):
    """
    Halmos: if x is the only value at k and c ≠ F x, no step lands on (k⁺, c).
    A step (m, t) ↦ (m⁺, F t) onto (k⁺, c) needs m = k, so t = x and c = F x.
    """
    X, a, F, k, x, c = l.fixes()
    l.intros()
    m, t = l.fixes()
    l.intros()
    l.intro()
    l.have(elem(m, omega), by=[nat_rec_le_prod(X, a, F), le.defn, pair_elem_prod])
    l.have(And(succ(m) == succ(k), F[t] == c), by=[zf.pair_inj])
    l.have(m == k, by=[succ_inj(m, k)])  # Peano V
    l.auto()


def unique_value(u, n):
    """There is exactly one x with (n, x) ∈ u."""
    return Exists(x, And(elem(pair(n, x), u), ForAll(y, elem(pair(n, y), u), y == x)))


@Theorem(
    ForAll(
        [X, a, F],
        elem(a, X),
        maps_to(F, X, X),
        ForAll(n, elem(n, omega), unique_value(nat_rec(X, a, F), n)),
    )
)
def nat_rec_unique_value(l):
    """Halmos: by induction, u has exactly one value at each n ∈ ω."""
    X, a, F = l.fixes()
    u = nat_rec(X, a, F)
    l.intros()
    n = l.fix()
    l.intro()
    l.induct(n, using=induct_omega)

    # 0 ∈ S: (0, a) ∈ u. If not unique, then (0, b) ∈ u for some b distinct from a.
    l.exists(a)
    l.split()
    l.auto(by=[nat_rec_closed(X, a, F), rec_closed.defn])
    b = l.fix()
    l.intro()
    l.contra()
    # The diminished set u - {(0, b)} still contains (0, a), and since n⁺ ≠ 0
    # no step lands on (0, b).
    p0 = pair(zero, b)
    l.have(pair(zero, a) != p0, by=[zf.pair_inj])
    l.have(
        ForAll([m, t], elem(pair(m, t), u - sing(p0)), pair(succ(m), F[t]) != p0),
        by=[zf.pair_inj, succ_ne_zero],
    )
    l.auto(by=[not_elem_nat_rec_of_sub_sing(X, a, F, p0)])

    # n ∈ S → n⁺ ∈ S: if x is the unique value at k, then (k⁺, F x) ∈ u.
    k = l.fix()
    _, ih = l.intros()
    x0, _ = l.obtain(ih)
    l.exists(F[x0])
    l.split()
    l.auto(by=[nat_rec_closed(X, a, F), rec_closed.defn])
    # If not unique, then (k⁺, c) ∈ u for some c different from F x.
    c = l.fix()
    l.intro()
    l.contra()
    # The diminished set u - {(k⁺, c)} still contains (0, a) since k⁺ ≠ 0,
    # and no step lands on (k⁺, c).
    p1 = pair(succ(k), c)
    l.have(pair(zero, a) != p1, by=[zf.pair_inj, succ_ne_zero])
    l.have(
        ForAll([m, t], elem(pair(m, t), u - sing(p1)), pair(succ(m), F[t]) != p1),
        by=[nat_rec_step_ne(X, a, F, k, x0, c), elem_sub],
    )
    l.auto(by=[not_elem_nat_rec_of_sub_sing(X, a, F, p1)])


@Theorem(
    ForAll([X, a, F], elem(a, X), maps_to(F, X, X), is_func(nat_rec(X, a, F), omega, X))
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
    ForAll([X, a, F], elem(a, X), maps_to(F, X, X), app(nat_rec(X, a, F), zero) == a),
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
        maps_to(F, X, X),
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
