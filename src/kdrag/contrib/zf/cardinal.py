"""
Uses of choice for sizes of sets (Halmos §23-25): every infinite set has a part
equivalent to ω, a countable union of countable sets is countable, and the
cardinal number card(X) is the least ordinal equivalent to X. Any two sets are
comparable, and X ≾ Y exactly when card(X) ⊆ card(Y).
"""

from kdrag import Theorem, define
from kdrag.smt import (
    And,
    ArraySort,
    BoolSort,
    Consts,
    Eq,
    Exists,
    ForAll,
    If,
    Implies,
    Lambda,
    Not,
    Or,
)
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import (
    ZFSet,
    bigunion,
    elem,
    le,
    pair,
    pow,
    prod,
    sep,
    sing,
    succ,
    zero,
)
from kdrag.contrib.zf.count import counting_theorem, ord_of
from kdrag.contrib.zf.ordinal import (
    is_ordinal,
    is_ordinal_of_elem,
    is_ordinal_succ,
    nat_is_ordinal,
    omega_is_ordinal,
    the,
    the_eq,
)
from kdrag.contrib.zf.ordset import (
    exists_least_of_ordinals,
    ordinal_comparable,
    ordinal_le_of_elem,
    ordinal_not_elem_self,
)
from kdrag.contrib.zf.order import nat_le
from kdrag.contrib.zf.sim import is_similarity, similar
from kdrag.contrib.zf.card import (
    dominated,
    dominated_of_equivalent,
    dominated_of_le,
    dominated_trans,
    schroeder_bernstein,
)
from kdrag.contrib.zf.choice import exists_choice_on, is_choice_on
from kdrag.contrib.zf.countable import (
    countable,
    omega_dominated_of_well_order,
    prod_omega_equivalent,
)
from kdrag.contrib.zf.finite import (
    equivalent,
    equivalent_refl,
    equivalent_symm,
    equivalent_trans,
    eq_of_equivalent_le_of_finite,
    finite,
    image,
    inv,
    inv_apply,
    nat_eq_of_equivalent,
    omega_infinite,
)
from kdrag.contrib.zf.fun import (
    app,
    app_elem,
    app_graph,
    bij_on,
    elem_prod_iff,
    elem_sub,
    graph,
    inj_on,
    is_func,
    is_func_graph,
    maps_to,
    pair_elem_prod,
    pfst,
    surj_on,
)
from kdrag.contrib.zf.nat import (
    elem_succ_self,
    exists_eq_succ_of_ne_zero,
    is_transitive,
    nat_not_elem_self,
    omega,
    omega_is_transitive,
    omega_succ,
    omega_zero,
    succ_inj,
    succ_ne_zero,
)
from kdrag.contrib.zf.poset import is_least, is_well_order, nat_le_rel
from kdrag.contrib.zf.wellord import exists_well_order
from kdrag.contrib.zf._sep import define_sep

A, B, C, D, K, X, Y, g, x, y = Consts("A B C D K X Y g x y", ZFSet)
n = Consts("n", ZFSet)[0]
F = Consts("F", ArraySort(ZFSet, ZFSet))[0]
R = Consts("R", ArraySort(ZFSet, ZFSet, BoolSort()))[0]


@Theorem(ForAll(X, Not(finite(X)), dominated(omega, X)))
def omega_dominated_of_infinite(l):
    """Halmos: every infinite set has a subset equivalent to ω. Well order it."""
    X = l.fix()
    l.intro()
    l.have(Exists(R, is_well_order(R, X)), by=[exists_well_order(X)])
    R0, _ = l.obtain(-1)
    l.auto(by=[omega_dominated_of_well_order(R0, X)])


# The one-to-one set functions from A into B.
injs = define(
    "injs",
    [A, B],
    sep(
        pow(prod(A, B)),
        Lambda(
            g,
            And(
                is_func(g, A, B),
                ForAll([x, y], elem(x, A), elem(y, A), app(g, x) == app(g, y), x == y),
            ),
        ),
    ),
)


@Theorem(
    ForAll(
        [A, B, g],
        elem(g, injs(A, B))
        == And(
            is_func(g, A, B),
            ForAll([x, y], elem(x, A), elem(y, A), app(g, x) == app(g, y), x == y),
        ),
    )
)
def elem_injs(l):
    A, B, g0 = l.fixes()
    l.unfold(injs)
    l.rw(zf.elem_sep)
    l.simp()
    l.auto(by=[zf.elem_pow, is_func.defn])


@Theorem(ForAll([A, B], dominated(A, B), injs(A, B) != zf.emp))
def injs_ne_emp(l):
    """The graph of a one-to-one HOL map is a one-to-one set function."""
    A, B = l.fixes()
    l.intro()
    l.unfold(dominated, at=0)
    F0, _ = l.obtain(0)
    G0 = graph(F0, A, B)
    l.have(is_func(G0, A, B), by=[is_func_graph(F0, A, B)])
    l.have(elem(G0, injs(A, B)), by=[elem_injs(A, B, G0), app_graph, inj_on.defn])
    l.auto(by=[zf.elem_emp(G0)])


# The members of C that contain x.
holders, elem_holders = define_sep("holders", [C, x], C, A, elem(x, A))


@Theorem(
    ForAll(
        C,
        countable(C),
        ForAll(A, elem(A, C), countable(A)),
        countable(bigunion(C)),
    )
)
def countable_bigunion(l):
    """Halmos §23: a countable union of countable sets is countable. Choose a
    member s(x) of C holding each x, and a one-to-one h(A) : A → ω for each
    A ∈ C. With C one-to-one into ω by c, x ↦ (c(s x), h(s x)(x)) maps ⋃C
    one-to-one into ω × ω ~ ω."""
    C = l.fix()
    l.intros()
    U = bigunion(C)
    W = prod(omega, omega)
    P = pow(prod(U, omega))
    l.unfold(countable, at=0)
    l.unfold(dominated, at=0)
    c0, _ = l.obtain(0)
    l.have(Exists(g, is_choice_on(g, P)), by=[exists_choice_on(P)])
    f1, _ = l.obtain(-1)
    l.have(Exists(g, is_choice_on(g, C)), by=[exists_choice_on(C)])
    f2, _ = l.obtain(-1)

    def h(A):
        return app(f1, injs(A, omega))

    def s(x):
        return app(f2, holders(C, x))

    # h(A) is a one-to-one function from A into ω.
    l.have(ForAll(A, elem(A, C), elem(h(A), injs(A, omega))))
    A0 = l.fix()
    l.intro()
    l.have(injs(A0, omega) != zf.emp, by=[injs_ne_emp, countable.defn(A0)])
    l.have(injs(A0, omega) <= P)
    l.rw(le.defn)
    g0 = l.fix()
    l.intro()
    l.have(g0 <= prod(A0, omega), by=[elem_injs(A0, omega, g0), is_func.defn])
    l.rw(zf.elem_pow)
    l.rw(le.defn)
    p0 = l.fix()
    l.intro()
    l.auto(
        by=[
            le.defn(g0, prod(A0, omega)),
            elem_prod_iff(A0, omega, p0),
            elem_prod_iff(U, omega, p0),
            zf.bigunion_ax(C, pfst(p0)),
        ]
    )
    l.auto(by=[is_choice_on.defn(f1, P)])
    # s(x) is a member of C that holds x.
    l.have(ForAll(x, elem(x, U), And(elem(s(x), C), elem(x, s(x)))))
    x0 = l.fix()
    l.intro()
    Hx = holders(C, x0)
    l.have(Exists(A, elem(A, Hx)), by=[zf.bigunion_ax(C, x0), elem_holders])
    A1, _ = l.obtain(-1)
    l.have(Hx != zf.emp, by=[zf.elem_emp(A1)])
    l.have(Hx <= C, by=[le.defn, elem_holders])
    l.have(elem(s(x0), Hx), by=[is_choice_on.defn(f2, C)])
    l.auto(by=[elem_holders(C, x0, s(x0))])

    Phi = Lambda(x, pair(c0[s(x)], app(h(s(x)), x)))
    l.have(dominated(U, W))
    l.unfold(dominated)
    l.exists(Phi)
    l.split()
    l.unfold(maps_to)
    x1 = l.fix()
    l.intro()
    l.simp()
    l.auto(
        by=[
            pair_elem_prod,
            maps_to.defn(c0, C, omega),
            elem_injs(s(x1), omega, h(s(x1))),
            app_elem(h(s(x1)), s(x1), omega, x1),
        ]
    )
    l.unfold(inj_on)
    x1, x2 = l.fixes()
    l.intros()
    l.simp(at=-1)
    l.have(s(x1) == s(x2), by=[zf.pair_inj, inj_on.defn(c0, C)])
    l.auto(by=[zf.pair_inj, elem_injs(s(x1), omega, h(s(x1)))])
    l.unfold(countable)
    l.auto(
        by=[
            dominated_trans(U, W, omega),
            prod_omega_equivalent,
            equivalent.defn(W, omega),
            bij_on.defn,
            dominated.defn(W, omega),
        ]
    )


# Cardinal numbers (Halmos §25): an ordinal equivalent to X and to no smaller
# ordinal.
is_card_of = define(
    "is_card_of",
    [K, X],
    And(
        is_ordinal(K),
        equivalent(X, K),
        ForAll(B, elem(B, K), Not(equivalent(X, B))),
    ),
)
# The ordinals in A that are equivalent to X.
equivs_in, elem_equivs_in = define_sep("equivs_in", [A, X], A, B, equivalent(X, B))


@Theorem(ForAll(X, Exists(K, is_card_of(K, X))))
def exists_card_of(l):
    """Halmos: well order X; it is equivalent to an ordinal α, and the least
    ordinal in α⁺ equivalent to X is a cardinal number of X."""
    X = l.fix()
    l.have(Exists(R, is_well_order(R, X)), by=[exists_well_order(X)])
    R0, _ = l.obtain(-1)
    a0 = ord_of(R0, X)
    l.have(
        And(is_ordinal(a0), similar(R0, X, nat_le_rel, a0)),
        by=[counting_theorem(R0, X)],
    )
    l.have(Exists(F, is_similarity(F, R0, X, nat_le_rel, a0)), by=[similar.defn])
    g0, _ = l.obtain(-1)
    l.have(equivalent(X, a0), by=[equivalent.defn, is_similarity.defn])
    S = succ(a0)
    E = equivs_in(S, X)
    l.have(is_ordinal(S), by=[is_ordinal_succ(a0)])
    l.have(ForAll(x, elem(x, S), is_ordinal(x)), by=[is_ordinal_of_elem])
    l.have(E <= S, by=[le.defn, elem_equivs_in])
    l.have(E != zf.emp, by=[elem_equivs_in(S, X, a0), elem_succ_self, zf.elem_emp])
    l.have(Exists(K, is_least(nat_le_rel, E, K)), by=[exists_least_of_ordinals(S, E)])
    k0, _ = l.obtain(-1)
    l.have(elem(k0, E), by=[is_least.defn])
    l.exists(k0)
    l.unfold(is_card_of)
    l.split()
    l.auto(by=[elem_equivs_in, is_ordinal_of_elem(S, k0)])
    l.auto(by=[elem_equivs_in])
    # B ∈ κ lies in α⁺ too, so X ~ B would give κ ≤ B ∈ κ.
    b0 = l.fix()
    l.intros()
    l.have(elem(k0, S), by=[elem_equivs_in])
    l.have(k0 <= S, by=[ordinal_le_of_elem(S, k0)])
    l.have(is_ordinal(k0), by=[is_ordinal_of_elem(S, k0)])
    l.have(elem(b0, S), by=[le.defn(k0, S)])
    l.have(
        Not(elem(k0, b0)),
        by=[ordinal_le_of_elem(k0, b0), le.defn, ordinal_not_elem_self(S, k0)],
    )
    l.auto(
        by=[
            elem_equivs_in(S, X, b0),
            is_least.defn(nat_le_rel, E, k0),
            nat_le.defn,
            ordinal_not_elem_self(S, k0),
        ]
    )


@Theorem(ForAll([X, A, B], is_card_of(A, X), is_card_of(B, X), A == B))
def card_of_unique(l):
    """Comparable ordinals: the smaller one would be equivalent to X."""
    X, A, B = l.fixes()
    l.intros()
    l.auto(by=[is_card_of.defn, ordinal_comparable(A, B)])


card = define("card", [X], the(Lambda(K, is_card_of(K, X))))


@Theorem(ForAll([X, K], is_card_of(K, X), card(X) == K))
def card_eq_of(l):
    X, K = l.fixes()
    l.intro()
    l.unfold(card)
    P = Lambda(K, is_card_of(K, X))
    l.auto(by=[the_eq(P, K), card_of_unique])


@Theorem(ForAll(X, is_card_of(card(X), X)))
def card_spec(l):
    X = l.fix()
    l.have(Exists(K, is_card_of(K, X)), by=[exists_card_of(X)])
    k0, _ = l.obtain(-1)
    l.auto(by=[card_eq_of(X, k0)])


@Theorem(ForAll([X, Y], (card(X) == card(Y)) == equivalent(X, Y)))
def card_eq(l):
    """Halmos: equivalent sets have the same cardinal number, and conversely."""
    X, Y = l.fixes()
    l.have(is_card_of(card(X), X), by=[card_spec])
    l.have(is_card_of(card(Y), Y), by=[card_spec])
    l.split()
    l.intro()
    l.auto(
        by=[
            is_card_of.defn,
            equivalent_symm(Y, card(Y)),
            equivalent_trans(X, card(X), Y),
        ]
    )
    # card(Y) is a cardinal number of X as well.
    l.intro()
    l.have(is_card_of(card(Y), X))
    l.unfold(is_card_of)
    l.split()
    l.auto(by=[is_card_of.defn])
    l.auto(by=[is_card_of.defn, equivalent_trans(X, Y, card(Y))])
    b0 = l.fix()
    l.intros()
    l.auto(
        by=[
            is_card_of.defn(card(Y), Y),
            equivalent_symm(X, Y),
            equivalent_trans(Y, X, b0),
        ]
    )
    l.auto(by=[card_eq_of(X, card(Y))])


@Theorem(ForAll(n, elem(n, omega), card(n) == n))
def card_nat(l):
    """A natural number is its own cardinal number: it is equivalent to no
    smaller natural number."""
    n0 = l.fix()
    l.intro()
    l.have(is_card_of(n0, n0))
    l.unfold(is_card_of)
    l.split()
    l.auto(by=[nat_is_ordinal])
    l.auto(by=[equivalent_refl])
    b0 = l.fix()
    l.intro()
    l.have(elem(b0, omega), by=[omega_is_transitive, is_transitive.defn, le.defn])
    l.auto(by=[nat_eq_of_equivalent(n0, b0), nat_not_elem_self(b0)])
    l.auto(by=[card_eq_of(n0, n0)])


@Theorem(card(omega) == omega)
def card_omega(l):
    """ℵ₀ = ω: ω is equivalent to no natural number, as it is infinite."""
    l.have(is_card_of(omega, omega))
    l.unfold(is_card_of)
    l.split()
    l.auto(by=[omega_is_ordinal])
    l.auto(by=[equivalent_refl])
    l.fix()
    l.intro()
    l.auto(by=[omega_infinite, finite.defn(omega)])
    l.auto(by=[card_eq_of(omega, omega)])


@Theorem(ForAll([X, Y], card(X) <= card(Y), dominated(X, Y)))
def dominated_of_card_le(l):
    """X ~ card(X) ⊆ card(Y) ~ Y."""
    X, Y = l.fixes()
    l.intro()
    cX, cY = card(X), card(Y)
    l.have(equivalent(X, cX), by=[card_spec(X), is_card_of.defn])
    l.have(equivalent(cY, Y), by=[card_spec(Y), is_card_of.defn, equivalent_symm])
    l.have(
        dominated(X, cY),
        by=[
            dominated_of_equivalent(X, cX),
            dominated_of_le(cY, cX),
            dominated_trans(X, cX, cY),
        ],
    )
    l.auto(by=[dominated_of_equivalent(cY, Y), dominated_trans(X, cY, Y)])


@Theorem(ForAll([X, Y], dominated(X, Y) == (card(X) <= card(Y))))
def card_le_iff(l):
    """Halmos §25: X ≾ Y iff card(X) ≤ card(Y). If card(Y) < card(X), then
    also Y ≾ X, and Schröder-Bernstein gives card(X) = card(Y)."""
    X, Y = l.fixes()
    cX, cY = card(X), card(Y)
    l.split()
    l.intro()
    l.contra()
    l.have(is_ordinal(cX), by=[card_spec(X), is_card_of.defn])
    l.have(is_ordinal(cY), by=[card_spec(Y), is_card_of.defn])
    l.have(
        elem(cY, cX),
        by=[ordinal_comparable(cX, cY), ordinal_le_of_elem(cY, cX), le.defn],
    )
    l.have(dominated(Y, X), by=[dominated_of_card_le(Y, X), ordinal_le_of_elem(cX, cY)])
    l.have(cX == cY, by=[schroeder_bernstein(X, Y), card_eq(X, Y)])
    l.auto(by=[ordinal_not_elem_self(cX, cY)])
    l.auto(by=[dominated_of_card_le(X, Y)])


@Theorem(ForAll([X, Y], Or(dominated(X, Y), dominated(Y, X))))
def embedding_total(l):
    """Halmos §25: any two sets are comparable, as their cardinal numbers are."""
    X, Y = l.fixes()
    cX, cY = card(X), card(Y)
    l.have(is_ordinal(cX), by=[card_spec(X), is_card_of.defn])
    l.have(is_ordinal(cY), by=[card_spec(Y), is_card_of.defn])
    l.auto(
        by=[
            ordinal_comparable(cX, cY),
            ordinal_le_of_elem(cY, cX),
            ordinal_le_of_elem(cX, cY),
            le.defn,
            dominated_of_card_le(X, Y),
            dominated_of_card_le(Y, X),
        ]
    )


@Theorem(
    ForAll(
        X,
        Not(finite(X)),
        Exists(Y, And(Y <= X, Y != X, equivalent(X, Y))),
    )
)
def exists_equivalent_ssubset_of_infinite(l):
    """Halmos §24: an infinite set is equivalent to a proper subset. With
    e : ω → X one-to-one, send each e(n) to e(n + 1) and fix the other points;
    this maps X onto X − {e(0)}."""
    X = l.fix()
    l.intro()
    l.have(dominated(omega, X), by=[omega_dominated_of_infinite(X)])
    l.have(Exists(F, And(maps_to(F, omega, X), inj_on(F, omega))), by=[dominated.defn])
    e0, _ = l.obtain(-1)
    I = inv(e0, omega)
    Img = image(e0, omega, X)
    # The image of e is the e(n), and I recovers n.
    l.have(
        ForAll(
            x,
            elem(x, Img) == And(elem(x, X), Exists(n, And(elem(n, omega), e0[n] == x))),
        ),
        by=[image.defn, zf.elem_sep],
    )
    l.have(ForAll(x, elem(x, Img), And(elem(I[x], omega), e0[I[x]] == x)))
    x0 = l.fix()
    l.intro()
    l.have(Exists(n, And(elem(n, omega), e0[n] == x0)))
    l.auto()
    n0, _ = l.obtain(-1)
    l.auto(by=[inv_apply(e0, omega, n0)])
    l.have(ForAll(n, elem(n, omega), elem(e0[n], Img)), by=[maps_to.defn])
    e_0 = e0[zero]
    l.have(elem(e_0, Img), by=[omega_zero])
    Y = X - sing(e_0)
    S = Lambda(x, If(elem(x, Img), e0[succ(I[x])], x))
    l.exists(Y)
    l.split()
    l.auto(by=[le.defn, elem_sub])
    l.auto(by=[elem_sub(e_0, X, sing(e_0)), zf.elem_sing])
    l.unfold(equivalent)
    l.exists(S)
    l.unfold(bij_on)
    l.split()
    # S lands in X − {e(0)}: e(n + 1) ≠ e(0) as n + 1 ≠ 0.
    l.unfold(maps_to)
    x1 = l.fix()
    l.intro()
    l.simp()
    l.cases(elem(x1, Img), Not(elem(x1, Img)))
    k1 = I[x1]
    l.auto(
        by=[
            elem_sub,
            zf.elem_sing,
            omega_succ(k1),
            omega_zero,
            maps_to.defn(e0, omega, X),
            inj_on.defn(e0, omega),
            succ_ne_zero(k1),
        ]
    )
    l.auto(by=[elem_sub, zf.elem_sing])
    # One-to-one: shifted points stay in the image, the others are fixed.
    l.unfold(inj_on)
    x1, x2 = l.fixes()
    l.intros()
    l.simp(at=-1)
    k1, k2 = I[x1], I[x2]
    l.have(Implies(elem(x1, Img), elem(e0[succ(k1)], Img)), by=[omega_succ(k1)])
    l.have(Implies(elem(x2, Img), elem(e0[succ(k2)], Img)), by=[omega_succ(k2)])
    l.auto(
        by=[
            omega_succ(k1),
            omega_succ(k2),
            inj_on.defn(e0, omega),
            succ_inj(k1, k2),
        ]
    )
    # Onto: y = e(k) with k ≠ 0 is S(e(j)) for k = j + 1; other y are fixed.
    l.unfold(surj_on)
    y0 = l.fix()
    l.intro()
    l.cases(elem(y0, Img), Not(elem(y0, Img)))
    k0 = I[y0]
    l.have(k0 != zero, by=[elem_sub, zf.elem_sing])
    l.have(
        Exists(n, And(elem(n, omega), k0 == succ(n))),
        by=[exists_eq_succ_of_ne_zero(k0)],
    )
    j0, _ = l.obtain(-1)
    l.exists(e0[j0])
    l.simp()
    l.auto(by=[inv_apply(e0, omega, j0), maps_to.defn, le.defn, elem_sub, zf.elem_sing])
    l.exists(y0)
    l.simp()
    l.auto(by=[elem_sub])


@Theorem(
    ForAll(
        X,
        Eq(Not(finite(X)), Exists(Y, And(Y <= X, Y != X, equivalent(X, Y)))),
    )
)
def infinite_iff_equivalent_ssubset(l):
    """Halmos §24: a set is infinite iff it is equivalent to a proper subset."""
    X = l.fix()
    l.split()
    l.auto(by=[exists_equivalent_ssubset_of_infinite(X)])
    l.intro()
    Y0, _ = l.obtain(-1)
    l.auto(by=[eq_of_equivalent_le_of_finite(X, Y0)])
