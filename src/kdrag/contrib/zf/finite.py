"""
Equivalent sets and finite sets (Halmos §13).

`equivalent(A, B)` holds when some one-to-one correspondence maps A onto B.
Correspondences are HOL functions `ZFSet → ZFSet` (`fun.bij_on`).
"""

from kdrag import Theorem, define, prove
from kdrag.smt import And, ArraySort, Consts, Exists, ForAll, If, Lambda, Not
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import ZFSet, bigunion, elem, le, sep, sing, succ, zero
from kdrag.contrib.zf.fun import (
    bigunion_sing,
    bij_on,
    bij_on_of_inverse,
    elem_sub,
    inj_on,
    maps_to,
    surj_on,
)
from kdrag.contrib.zf.nat import (
    elem_succ,
    elem_succ_self,
    exists_eq_succ_of_ne_zero,
    induct_omega,
    is_transitive,
    nat_not_elem_self,
    omega,
    omega_is_transitive,
    omega_succ,
    succ_inj,
    succ_ne_zero,
)
from kdrag.contrib.zf.order import comparable, elem_iff_le_ne, nat_comparable

A, B, C, E, X, Y, a, b, k, m, n, x, y, z = Consts("A B C E X Y a b k m n x y z", ZFSet)
F, G = Consts("F G", ArraySort(ZFSet, ZFSet))

equivalent = define("equivalent", [A, B], Exists(F, bij_on(F, A, B)))


@Theorem(
    ForAll(
        [F, G, X, Y],
        maps_to(F, X, Y),
        maps_to(G, Y, X),
        ForAll(x, elem(x, X), G[F[x]] == x),
        ForAll(y, elem(y, Y), F[G[y]] == y),
        equivalent(X, Y),
    )
)
def equivalent_of_inverse(l):
    F, G, X, Y = l.fixes()
    l.intros()
    l.unfold(equivalent)
    l.exists(F)
    l.auto(by=[bij_on_of_inverse(F, G, X, Y)])


bij_on_id = prove(
    ForAll(A, bij_on(Lambda(x, x), A, A)),
    by=[bij_on.defn, maps_to.defn, inj_on.defn, surj_on.defn],
)
bij_on_comp = prove(
    ForAll(
        [F, G, A, B, C],
        bij_on(F, A, B),
        bij_on(G, B, C),
        bij_on(Lambda(x, G[F[x]]), A, C),
    ),
    by=[bij_on.defn, maps_to.defn, inj_on.defn, surj_on.defn],
)


# The inverse of a one-to-one correspondence needs no choice: for y in the range,
# {x ∈ A | F x = y} is a singleton {x}, and ⋃{x} = x (Halmos §10).
inv = define("inv", [F, A], Lambda(y, bigunion(sep(A, Lambda(x, F[x] == y)))))


@Theorem(ForAll([F, A, x], inj_on(F, A), elem(x, A), inv(F, A)[F[x]] == x))
def inv_apply(l):
    F, A, x = l.fixes()
    l.intros()
    l.unfold(inv)
    l.simp()
    # Injectivity makes {z ∈ A | F z = F x} the singleton {x}.
    l.have(sep(A, Lambda(z, F[z] == F[x])) == sing(x))
    l.rw(zf.ext_ax)
    l.fix()
    l.rw(zf.elem_sep).rw(zf.elem_sing)
    l.auto(by=[inj_on.defn(F, A)])
    l.auto(by=[bigunion_sing(x)])


@Theorem(
    ForAll(
        [F, A, B, y],
        bij_on(F, A, B),
        elem(y, B),
        And(elem(inv(F, A)[y], A), F[inv(F, A)[y]] == y),
    )
)
def inv_elem(l):
    F, A, B, y = l.fixes()
    l.intros()
    # y = F x for some x ∈ A, and inv(F, A) sends F x back to x.
    l.have(Exists(x, And(elem(x, A), F[x] == y)), by=[bij_on.defn, surj_on.defn])
    x0, _ = l.obtain(-1)
    l.auto(by=[inv_apply(F, A, x0), bij_on.defn])


bij_on_inv = prove(
    ForAll([F, A, B], bij_on(F, A, B), bij_on(inv(F, A), B, A)),
    by=[bij_on.defn, maps_to.defn, inj_on.defn, surj_on.defn, inv_elem, inv_apply],
)


equivalent_refl = prove(ForAll(A, equivalent(A, A)), by=[equivalent.defn, bij_on_id])
equivalent_symm = prove(
    ForAll([A, B], equivalent(A, B), equivalent(B, A)),
    by=[equivalent.defn, bij_on_inv],
)


@Theorem(ForAll([A, B, C], equivalent(A, B), equivalent(B, C), equivalent(A, C)))
def equivalent_trans(l):
    A, B, C = l.fixes()
    l.intros()
    l.unfold(equivalent)
    l.unfold(equivalent, at=0)
    l.unfold(equivalent, at=1)
    F0, _ = l.obtain(0)
    G0, _ = l.obtain(1)
    l.exists(Lambda(x, G0[F0[x]]))
    l.auto(by=[bij_on_comp(F0, G0, A, B, C)])


# Halmos: "a set can be equivalent to a proper subset of itself".


@Theorem(bij_on(Lambda(x, succ(x)), omega, omega - sing(zero)))
def bij_on_succ_omega(l):
    """n ↦ n⁺ is a one-to-one correspondence from ω onto the nonzero naturals."""
    l.unfold(bij_on)
    l.split()
    l.auto(by=[maps_to.defn, elem_sub, zf.elem_sing, omega_succ, succ_ne_zero])
    l.auto(by=[inj_on.defn, succ_inj])
    l.auto(by=[surj_on.defn, elem_sub, zf.elem_sing, exists_eq_succ_of_ne_zero])


omega_equivalent_sub_zero = prove(
    equivalent(omega, omega - sing(zero)), by=[equivalent.defn, bij_on_succ_omega]
)


# Tools for the pigeonhole principle

swap = define("swap", [a, b], Lambda(x, If(x == a, b, If(x == b, a, x))))
bij_on_swap = prove(
    ForAll([a, b, A], elem(a, A), elem(b, A), bij_on(swap(a, b), A, A)),
    by=[swap.defn, bij_on.defn, maps_to.defn, inj_on.defn, surj_on.defn],
)
bij_on_sub_sing = prove(
    ForAll(
        [F, A, B, a],
        bij_on(F, A, B),
        elem(a, A),
        bij_on(F, A - sing(a), B - sing(F[a])),
    ),
    by=[bij_on.defn, maps_to.defn, inj_on.defn, surj_on.defn, elem_sub, zf.elem_sing],
)


@Theorem(ForAll(n, elem(n, omega), succ(n) - sing(n) == n))
def succ_sub_sing_self(l):
    n = l.fix()
    l.intro()
    l.rw(zf.ext_ax)
    z = l.fix()
    # z ∈ n⁺ and z ≠ n iff z ∈ n, since n ∉ n.
    l.auto(
        by=[
            elem_sub(z, succ(n), sing(n)),
            zf.elem_sing(z, n),
            elem_succ(z, n),
            nat_not_elem_self(n),
        ]
    )


@Theorem(ForAll(n, elem(n, omega), ForAll(E, E <= n, equivalent(n, E), E == n)))
def nat_eq_of_equivalent_le(l):
    """Halmos: a natural number is not equivalent to a proper subset of itself."""
    n = l.fix()
    l.intro()
    l.induct(n, using=induct_omega)
    # n = 0: the only subset of 0 is 0.
    l.fix()
    l.intros()
    l.auto(by=[zf.ext_ax, le.defn, zero.defn, zf.elem_emp])

    # Suppose it holds for k, and F is a correspondence from k⁺ onto E ⊆ k⁺.
    k = l.fix()
    _, ih = l.intros()
    E = l.fix()
    l.intros()
    l.unfold(equivalent, at=-1)
    F0, _ = l.obtain(-1)
    l.have(elem(F0[k], E), by=[bij_on.defn, maps_to.defn, elem_succ_self])
    l.cases(elem(k, E), Not(elem(k, E)))

    # k ∈ E: swap F k with k, so the correspondence sends k to k. Removing k from
    # both sides, k is equivalent to E - {k} ⊆ k, so E - {k} = k and E = k⁺.
    G0 = Lambda(x, swap(F0[k], k)[F0[x]])
    l.have(bij_on(swap(F0[k], k), E, E), by=[bij_on_swap])
    l.have(bij_on(G0, succ(k), E), by=[bij_on_comp(F0, swap(F0[k], k), succ(k), E, E)])
    l.have(G0[k] == k, by=[swap.defn])
    l.have(
        bij_on(G0, k, E - sing(k)),
        by=[bij_on_sub_sing(G0, succ(k), E, k), elem_succ_self, succ_sub_sing_self(k)],
    )
    l.have(E - sing(k) <= k, by=[le.defn, elem_sub, zf.elem_sing, elem_succ])
    l.specialize(ih, E - sing(k), keep=True)
    l.have(E - sing(k) == k, by=[equivalent.defn(k, E - sing(k))])
    l.rw(zf.ext_ax)
    z = l.fix()
    l.auto(by=[elem_sub(z, E, sing(k)), zf.elem_sing(z, k), elem_succ(z, k)])

    # k ∉ E: then E ⊆ k, and F restricted to k is a correspondence onto
    # E - {F k} ⊆ k. So E - {F k} = k, but F k ∈ E ⊆ k: a contradiction.
    l.have(E <= k, by=[le.defn, elem_succ])
    l.have(
        bij_on(F0, k, E - sing(F0[k])),
        by=[bij_on_sub_sing(F0, succ(k), E, k), elem_succ_self, succ_sub_sing_self(k)],
    )
    l.have(E - sing(F0[k]) <= k, by=[le.defn, elem_sub])
    l.specialize(ih, E - sing(F0[k]), keep=True)
    l.have(E - sing(F0[k]) == k, by=[equivalent.defn(k, E - sing(F0[k]))])
    l.auto(by=[le.defn(E, k), elem_sub(F0[k], E, sing(F0[k])), zf.elem_sing])
    l.auto()  # the side goal n ∈ ω left by induct


finite = define("finite", [A], Exists(n, And(elem(n, omega), equivalent(A, n))))


@Theorem(ForAll([m, n], elem(m, omega), elem(n, omega), equivalent(m, n), m == n))
def nat_eq_of_equivalent(l):
    """Halmos: distinct naturals are not equivalent; the smaller is a proper subset."""
    m, n = l.fixes()
    l.intros()
    l.have(equivalent(n, m), by=[equivalent_symm])
    l.auto(
        by=[
            nat_comparable(m, n),
            comparable.defn(m, n),
            elem_iff_le_ne,
            nat_eq_of_equivalent_le(n),
            nat_eq_of_equivalent_le(m),
        ]
    )


finite_card_unique = prove(
    ForAll(
        [A, m, n],
        elem(m, omega),
        elem(n, omega),
        equivalent(A, m),
        equivalent(A, n),
        m == n,
    ),
    by=[equivalent_symm, equivalent_trans, nat_eq_of_equivalent],
)


# The image of A under F, inside a known codomain B.
image = define(
    "image", [F, A, B], sep(B, Lambda(y, Exists(x, And(elem(x, A), F[x] == y))))
)

bij_on_image = prove(
    ForAll(
        [F, A, B],
        maps_to(F, A, B),
        inj_on(F, A),
        bij_on(F, A, image(F, A, B)),
    ),
    by=[image.defn, zf.elem_sep, bij_on.defn, maps_to.defn, surj_on.defn],
)


@Theorem(Not(finite(omega)))
def omega_infinite(l):
    """Halmos §13 exercise: if ω ~ n, then n⁺ would be equivalent to a subset of n."""
    l.unfold(finite)
    l.intro()
    n0, _ = l.obtain(-1)
    l.have(Exists(F, bij_on(F, omega, n0)), by=[equivalent.defn])
    F0, _ = l.obtain(-1)
    # F restricted to n⁺ ⊆ ω is one-to-one into n, so n⁺ ~ F[n⁺] ⊆ n ⊆ n⁺.
    img = image(F0, succ(n0), n0)
    l.have(
        succ(n0) <= omega,
        by=[le.defn, elem_succ, omega_is_transitive, is_transitive.defn],
    )
    l.have(maps_to(F0, succ(n0), n0), by=[maps_to.defn, bij_on.defn, le.defn])
    l.have(inj_on(F0, succ(n0)), by=[inj_on.defn, bij_on.defn, le.defn])
    l.have(bij_on(F0, succ(n0), img), by=[bij_on_image])
    l.have(img <= succ(n0), by=[le.defn, image.defn, zf.elem_sep, elem_succ])
    l.have(
        img == succ(n0),
        by=[nat_eq_of_equivalent_le(succ(n0)), equivalent.defn, omega_succ],
    )
    # But n ∈ n⁺ = F[n⁺] ⊆ n, and n ∉ n.
    l.auto(
        by=[
            elem_succ_self(n0),
            image.defn(F0, succ(n0), n0),
            zf.elem_sep,
            nat_not_elem_self(n0),
        ]
    )


@Theorem(ForAll([X, Y], finite(X), Y <= X, equivalent(X, Y), Y == X))
def eq_of_equivalent_le_of_finite(l):
    """Halmos §24: a finite set is equivalent to no proper subset. With X ~ n by
    g, n ~ g[Y] ⊆ n, so g[Y] = n, and then every x ∈ X is in Y."""
    X, Y = l.fixes()
    l.intros()
    l.have(Exists(n, And(elem(n, omega), equivalent(X, n))), by=[finite.defn(X)])
    n0, _ = l.obtain(-1)
    l.have(Exists(F, bij_on(F, X, n0)), by=[equivalent.defn])
    g0, _ = l.obtain(-1)
    img = image(g0, Y, n0)
    l.have(maps_to(g0, Y, n0), by=[maps_to.defn, bij_on.defn, le.defn])
    l.have(inj_on(g0, Y), by=[inj_on.defn, bij_on.defn, le.defn])
    l.have(equivalent(Y, img), by=[bij_on_image(g0, Y, n0), equivalent.defn])
    l.have(
        equivalent(n0, img),
        by=[
            equivalent_symm(X, n0),
            equivalent_trans(n0, X, Y),
            equivalent_trans(n0, Y, img),
        ],
    )
    l.have(img <= n0, by=[le.defn, image.defn, zf.elem_sep])
    l.have(img == n0, by=[nat_eq_of_equivalent_le(n0)])
    # x ∈ X has g x ∈ n = g[Y], so g x = g y for some y ∈ Y, and x = y.
    l.have(X <= Y)
    l.rw(le.defn)
    x0 = l.fix()
    l.intro()
    l.have(elem(g0[x0], img), by=[bij_on.defn, maps_to.defn])
    l.have(Exists(y, And(elem(y, Y), g0[y] == g0[x0])), by=[image.defn, zf.elem_sep])
    y0, _ = l.obtain(-1)
    l.auto(by=[bij_on.defn, inj_on.defn(g0, X), le.defn(Y, X)])
    l.auto(by=[zf.ext_ax, le.defn])
