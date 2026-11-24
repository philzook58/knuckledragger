"""
Ordinal multiplication (Halmos §21).

The ordinal product of well ordered sets A and B is A × B ordered reverse
lexicographically: compare second coordinates, and first coordinates when the
second ones agree. αβ is the ordinal of the ordinal product of α and β.
"""

from kdrag import Theorem, define, define_const, prove
from kdrag.smt import (
    And,
    ArraySort,
    BoolSort,
    Consts,
    Exists,
    ForAll,
    If,
    Lambda,
    Or,
    Select,
)
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import ZFSet, elem, le, pair, prod, zero
from kdrag.contrib.zf.count import counting_theorem, ord_of, ord_of_eq
from kdrag.contrib.zf.fun import (
    bij_on,
    elem_prod_iff,
    inj_on,
    maps_to,
    pair_elem_prod,
    pfst,
    pfst_pair,
    psnd,
    psnd_pair,
    surj_on,
)
from kdrag.contrib.zf.nat import (
    elem_one,
    elem_succ_self,
    elem_two,
    nat_not_elem_self,
    omega,
    omega_zero,
    one,
    two,
    zero_ne_one,
)
from kdrag.contrib.zf.oarith import (
    oadd,
    oadd_spec,
    oplus,
    oplus_apply,
    osum_rel,
    osum_rel_inl_inl,
    osum_rel_inl_inr,
    osum_rel_inr_inr,
    osum_rel_pairs,
    similar_osum,
)
from kdrag.contrib.zf.order import (
    bit,
    bit_elem_bit,
    bit_elem_omega,
    comparable,
    exists_bit,
    nat_comparable,
    nat_elem_asymm,
    nat_le,
)
from kdrag.contrib.zf.ordinal import is_ordinal, nat_is_ordinal, omega_is_ordinal
from kdrag.contrib.zf.ordset import ordinal_well_order
from kdrag.contrib.zf.poset import (
    elem_seg_iff,
    omega_well_order,
    seg,
    exists_least,
    is_least,
    is_partial_order,
    is_well_order,
    nat_le_rel,
    partial_order_antisymm,
    partial_order_of_well_order,
    partial_order_refl,
    partial_order_trans,
)
from kdrag.contrib.zf.sim import (
    not_similarity_seg,
    similarity_comp,
    similarity_seg,
    is_order_embedding,
    is_similarity,
    similar,
    similar_refl,
    similar_symm,
    similar_trans,
)
from kdrag.contrib.zf.dsum import elem_osum_set, inl, inr, osum_set
from kdrag.contrib.zf._sep import define_sep

A, B, E, a, b, c, d, k, m, n, p, q, x, y = Consts("A B E a b c d k m n p q x y", ZFSet)
A2, B2 = Consts("A2 B2", ZFSet)
R, S, R2, S2 = Consts("R S R2 S2", ArraySort(ZFSet, ZFSet, BoolSort()))
f, g = Consts("f g", ArraySort(ZFSet, ZFSet))


oprod_le = define(
    "oprod_le",
    [R, S, p, q],
    Or(
        And(S[psnd(p), psnd(q)], psnd(p) != psnd(q)),
        And(psnd(p) == psnd(q), R[pfst(p), pfst(q)]),
    ),
)
oprod_rel = define("oprod_rel", [R, S], Lambda([p, q], oprod_le(R, S, p, q)))


@Theorem(
    ForAll(
        [R, S, a, b, c, d],
        oprod_rel(R, S)[pair(a, b), pair(c, d)]
        == Or(And(S[b, d], b != d), And(b == d, R[a, c])),
    )
)
def oprod_rel_pair(l):
    l.fixes()
    l.unfold(oprod_rel)
    l.simp()
    l.auto(by=[oprod_le.defn, pfst_pair, psnd_pair])


@Theorem(
    ForAll(
        [R, S, A, B],
        is_partial_order(R, A),
        is_partial_order(S, B),
        is_partial_order(oprod_rel(R, S), prod(A, B)),
    )
)
def oprod_partial_order(l):
    """The ordinal product order is a partial order."""
    R, S, A, B = l.fixes()
    l.intros()

    def rel(p, q):
        return oprod_rel_pair(R, S, pfst(p), psnd(p), pfst(q), psnd(q))

    l.unfold(is_partial_order)
    l.split()
    p0 = l.fix()
    l.intro()
    l.auto(
        by=[
            elem_prod_iff(A, B, p0),
            rel(p0, p0),
            partial_order_refl(R, A, pfst(p0)),
        ]
    )
    p1, q1 = l.fixes()
    l.intros()
    l.auto(
        by=[
            elem_prod_iff(A, B, p1),
            elem_prod_iff(A, B, q1),
            rel(p1, q1),
            rel(q1, p1),
            partial_order_antisymm(R, A, pfst(p1), pfst(q1)),
            partial_order_antisymm(S, B, psnd(p1), psnd(q1)),
        ]
    )
    # Transitivity needs antisymmetry in B: b ≤ d ≤ b' with b ≠ b' stays strict.
    p2, q2, r2 = l.fixes()
    l.intros()

    l.auto(
        by=[
            elem_prod_iff(A, B, p2),
            elem_prod_iff(A, B, q2),
            elem_prod_iff(A, B, r2),
            rel(p2, q2),
            rel(q2, r2),
            rel(p2, r2),
            partial_order_trans(R, A, pfst(p2), pfst(q2), pfst(r2)),
            partial_order_trans(S, B, psnd(p2), psnd(q2), psnd(r2)),
            partial_order_antisymm(S, B, psnd(p2), psnd(q2)),
        ]
    )


# For E ⊆ A × B: the second coordinates occurring in E, and the first
# coordinates paired with b.
snds, elem_snds = define_sep("snds", [E, B], B, b, Exists(a, elem(pair(a, b), E)))
fiber, elem_fiber = define_sep("fiber", [E, A, b], A, a, elem(pair(a, b), E))


@Theorem(
    ForAll(
        [R, S, A, B],
        is_well_order(R, A),
        is_well_order(S, B),
        is_well_order(oprod_rel(R, S), prod(A, B)),
    )
)
def oprod_well_order(l):
    """Halmos: the ordinal product of well ordered sets is well ordered. The least
    element of E has the least second coordinate b, and then the least first
    coordinate among the elements of E ending in b."""
    R, S, A, B = l.fixes()
    l.intros()
    X = prod(A, B)
    l.unfold(is_well_order)
    l.split()
    l.auto(
        by=[
            oprod_partial_order(R, S, A, B),
            partial_order_of_well_order(R, A),
            partial_order_of_well_order(S, B),
        ]
    )
    E0 = l.fix()
    l.intros()
    l.have(Exists(p, elem(p, E0)), by=[zf.not_emp_exists_elem(E0)])
    e0, _ = l.obtain(-1)
    l.have(elem(e0, X), by=[le.defn(E0, X)])
    # The least second coordinate b0.
    Bs = snds(E0, B)
    l.have(Bs <= B, by=[le.defn, elem_snds])
    l.have(
        elem(psnd(e0), Bs),
        by=[elem_snds(E0, B, psnd(e0)), elem_prod_iff(A, B, e0)],
    )
    l.have(Bs != zf.emp, by=[zf.elem_emp(psnd(e0))])
    l.have(Exists(b, is_least(S, Bs, b)), by=[exists_least(S, B, Bs)])
    b0, _ = l.obtain(-1)
    l.have(elem(b0, Bs), by=[is_least.defn(S, Bs, b0)])
    l.have(Exists(a, elem(pair(a, b0), E0)), by=[elem_snds(E0, B, b0)])
    a1, _ = l.obtain(-1)
    # The least first coordinate a0 paired with b0.
    As = fiber(E0, A, b0)
    l.have(As <= A, by=[le.defn, elem_fiber])
    l.have(
        elem(a1, As),
        by=[
            elem_fiber(E0, A, b0, a1),
            le.defn(E0, X),
            pair_elem_prod(a1, b0, A, B),
        ],
    )
    l.have(As != zf.emp, by=[zf.elem_emp(a1)])
    l.have(Exists(a, is_least(R, As, a)), by=[exists_least(R, A, As)])
    a0, _ = l.obtain(-1)
    l.exists(pair(a0, b0))
    l.unfold(is_least)
    l.split()
    l.auto(by=[is_least.defn(R, As, a0), elem_fiber(E0, A, b0, a0)])
    q0 = l.fix()
    l.intro()
    l.have(elem(q0, X), by=[le.defn(E0, X)])
    l.auto(
        by=[
            elem_prod_iff(A, B, q0),
            oprod_rel_pair(R, S, a0, b0, pfst(q0), psnd(q0)),
            is_least.defn(S, Bs, b0),
            is_least.defn(R, As, a0),
            elem_snds(E0, B, psnd(q0)),
            elem_fiber(E0, A, b0, pfst(q0)),
        ]
    )


# αβ is the ordinal number of the ordinal product of α and β.
otimes = oprod_rel(nat_le_rel, nat_le_rel)
omul = define("omul", [A, B], ord_of(otimes, prod(A, B)))


@Theorem(
    ForAll(
        [A, B],
        is_ordinal(A),
        is_ordinal(B),
        And(
            is_ordinal(omul(A, B)),
            similar(nat_le_rel, omul(A, B), otimes, prod(A, B)),
        ),
    )
)
def omul_spec(l):
    """αβ is an ordinal similar to α × β (the counting theorem)."""
    A, B = l.fixes()
    l.intros()
    X = prod(A, B)
    l.have(
        is_well_order(otimes, X),
        by=[
            oprod_well_order(nat_le_rel, nat_le_rel, A, B),
            ordinal_well_order(A),
            ordinal_well_order(B),
        ],
    )
    l.unfold(omul)
    l.auto(
        by=[
            counting_theorem(otimes, X),
            similar_symm(otimes, X, nat_le_rel, ord_of(otimes, X)),
        ]
    )


@Theorem(ForAll(R, ord_of(R, zf.emp) == zero))
def ord_of_emp(l):
    """The empty set is similar to the ordinal 0."""
    R = l.fix()
    l.have(similar(R, zf.emp, nat_le_rel, zero))
    l.unfold(similar)
    l.exists(Lambda(x, x))
    l.unfold(is_similarity)
    l.unfold(is_order_embedding)
    l.unfold(bij_on)
    l.auto(by=[zero.defn, zf.elem_emp, maps_to.defn, inj_on.defn, surj_on.defn])
    l.auto(by=[ord_of_eq(R, zf.emp, zero), nat_is_ordinal(zero), omega_zero, zero.defn])


@Theorem(ForAll(A, And(prod(A, zero) == zf.emp, prod(zero, A) == zf.emp)))
def prod_zero(l):
    """A × 0 = 0 × A = ∅, as an element would have a coordinate in ∅."""
    A = l.fix()
    l.split()
    l.rw(zf.ext_ax)
    p0 = l.fix()
    l.auto(
        by=[
            elem_prod_iff(A, zero, p0),
            zf.elem_emp(psnd(p0)),
            zf.elem_emp(p0),
            zero.defn,
        ]
    )
    l.rw(zf.ext_ax)
    p1 = l.fix()
    l.auto(
        by=[
            elem_prod_iff(zero, A, p1),
            zf.elem_emp(pfst(p1)),
            zf.elem_emp(p1),
            zero.defn,
        ]
    )


# Halmos: α0 = 0α = 0.
omul_zero = prove(
    ForAll(A, omul(A, zero) == zero), by=[omul.defn, prod_zero, ord_of_emp]
)
zero_omul = prove(
    ForAll(A, omul(zero, A) == zero), by=[omul.defn, prod_zero, ord_of_emp]
)


@Theorem(ForAll(A, is_ordinal(A), omul(A, one) == A))
def omul_one(l):
    """Halmos: α1 = α, by (x, 0) ↦ x."""
    A = l.fix()
    l.intro()
    X = prod(A, one)
    f = Lambda(p, pfst(p))
    # Every element of α × 1 is (x, 0) with x ∈ α.
    l.have(
        ForAll(p, elem(p, X), And(elem(pfst(p), A), p == pair(pfst(p), zero))),
        by=[elem_prod_iff, elem_one],
    )
    l.have(is_similarity(f, otimes, X, nat_le_rel, A))
    l.unfold(is_similarity)
    l.unfold(is_order_embedding)
    l.split()
    l.split()
    l.auto(by=[maps_to.defn(f, X, A)])
    p0, q0 = l.fixes()
    l.intros()
    l.simp()
    l.auto(
        by=[
            oprod_rel_pair(nat_le_rel, nat_le_rel, pfst(p0), zero, pfst(q0), zero),
            nat_le.defn,
        ]
    )
    l.unfold(bij_on)
    l.split()
    l.auto(by=[maps_to.defn(f, X, A)])
    l.unfold(inj_on)
    p1, q1 = l.fixes()
    l.intros()
    l.simp(at=-1)
    l.auto()
    l.unfold(surj_on)
    x0 = l.fix()
    l.intro()
    l.exists(pair(x0, zero))
    l.simp()
    l.auto(by=[pair_elem_prod(x0, zero, A, one), elem_one, pfst_pair])
    l.unfold(omul)
    l.auto(by=[ord_of_eq(otimes, X, A), similar.defn(otimes, X, nat_le_rel, A)])


@Theorem(ForAll(A, is_ordinal(A), omul(one, A) == A))
def one_omul(l):
    """Halmos: 1α = α, by (0, x) ↦ x."""
    A = l.fix()
    l.intro()
    X = prod(one, A)
    f = Lambda(p, psnd(p))
    # Every element of 1 × α is (0, x) with x ∈ α.
    l.have(
        ForAll(p, elem(p, X), And(elem(psnd(p), A), p == pair(zero, psnd(p)))),
        by=[elem_prod_iff, elem_one],
    )
    l.have(is_similarity(f, otimes, X, nat_le_rel, A))
    l.unfold(is_similarity)
    l.unfold(is_order_embedding)
    l.split()
    l.split()
    l.auto(by=[maps_to.defn(f, X, A)])
    p0, q0 = l.fixes()
    l.intros()
    l.simp()
    l.auto(
        by=[
            oprod_rel_pair(nat_le_rel, nat_le_rel, zero, psnd(p0), zero, psnd(q0)),
            nat_le.defn,
        ]
    )
    l.unfold(bij_on)
    l.split()
    l.auto(by=[maps_to.defn(f, X, A)])
    l.unfold(inj_on)
    p1, q1 = l.fixes()
    l.intros()
    l.simp(at=-1)
    l.auto()
    l.unfold(surj_on)
    x0 = l.fix()
    l.intro()
    l.exists(pair(zero, x0))
    l.simp()
    l.auto(by=[pair_elem_prod(zero, x0, one, A), elem_one, psnd_pair])
    l.unfold(omul)
    l.auto(by=[ord_of_eq(otimes, X, A), similar.defn(otimes, X, nat_le_rel, A)])


@Theorem(ForAll(A, is_ordinal(A), omul(A, two) == oadd(A, A)))
def omul_two(l):
    """Halmos: α2 = α + α. The ordinal product α × 2 and the ordinal sum α ⊕ α
    are the same ordered set."""
    A = l.fix()
    l.intro()
    X, Y = prod(A, two), osum_set(A, A)
    l.have(ForAll(p, elem(p, X) == elem(p, Y)))
    p1 = l.fix()
    l.auto(
        by=[
            elem_prod_iff(A, two, p1),
            elem_two(psnd(p1)),
            elem_osum_set(A, A, p1),
            psnd_pair(pfst(p1), zero),
            psnd_pair(pfst(p1), one),
        ]
    )
    l.have(is_similarity(Lambda(x, x), otimes, X, oplus, Y))
    l.unfold(is_similarity)
    l.unfold(is_order_embedding)
    l.unfold(bij_on)
    l.split()
    l.split()
    l.auto(by=[maps_to.defn])
    # (x, i) ≤ (y, j) iff i < j, or i = j and x ≤ y, in both orders.
    p0, q0 = l.fixes()
    l.intros()
    l.simp()
    l.auto(
        by=[
            elem_prod_iff(A, two, p0),
            elem_prod_iff(A, two, q0),
            elem_two(psnd(p0)),
            elem_two(psnd(q0)),
            oprod_rel_pair(
                nat_le_rel, nat_le_rel, pfst(p0), psnd(p0), pfst(q0), psnd(q0)
            ),
            oplus_apply(A, A, p0, q0),
            nat_le.defn,
            zf.pair_inj,
            zero_ne_one,
            elem_one(zero),
            zf.elem_emp,
            zero.defn,
        ]
    )
    l.auto(by=[maps_to.defn, inj_on.defn, surj_on.defn])
    l.have(
        And(is_ordinal(oadd(A, A)), similar(nat_le_rel, oadd(A, A), oplus, Y)),
        by=[oadd_spec(A, A)],
    )
    l.have(
        similar(otimes, X, nat_le_rel, oadd(A, A)),
        by=[
            similar.defn(otimes, X, oplus, Y),
            similar_symm(nat_le_rel, oadd(A, A), oplus, Y),
            similar_trans(otimes, X, oplus, Y, nat_le_rel, oadd(A, A)),
        ],
    )
    l.unfold(omul)
    l.auto(by=[ord_of_eq(otimes, X, oadd(A, A))])


# Similarities f: A → A' and g: B → B' act on each coordinate of A × B.
oprod_map = define("oprod_map", [f, g], Lambda(p, pair(f[pfst(p)], g[psnd(p)])))


@Theorem(
    ForAll(
        [f, g, R, A, R2, A2, S, B, S2, B2],
        is_similarity(f, R, A, R2, A2),
        is_similarity(g, S, B, S2, B2),
        is_similarity(
            oprod_map(f, g),
            oprod_rel(R, S),
            prod(A, B),
            oprod_rel(R2, S2),
            prod(A2, B2),
        ),
    )
)
def similarity_oprod(l):
    """Similar factors have similar ordinal products."""
    f, g, R, A, R2, A2, S, B, S2, B2 = l.fixes()
    l.intros()
    fd = [is_similarity.defn(f, R, A, R2, A2), is_order_embedding.defn(f, R, A, R2, A2)]
    gd = [is_similarity.defn(g, S, B, S2, B2), is_order_embedding.defn(g, S, B, S2, B2)]
    l.have(bij_on(f, A, A2), by=fd)
    l.have(bij_on(g, B, B2), by=gd)
    l.have(ForAll([a, b], elem(a, A), elem(b, A), R[a, b] == R2[f[a], f[b]]), by=fd)
    l.have(ForAll([a, b], elem(a, B), elem(b, B), S[a, b] == S2[g[a], g[b]]), by=gd)
    l.clear(is_similarity(f, R, A, R2, A2))
    l.clear(is_similarity(g, S, B, S2, B2))
    l.have(maps_to(f, A, A2), by=[bij_on.defn(f, A, A2)])
    l.have(maps_to(g, B, B2), by=[bij_on.defn(g, B, B2)])
    l.have(inj_on(g, B), by=[bij_on.defn(g, B, B2)])
    F = oprod_map(f, g)
    l.have(ForAll(p, F[p] == pair(f[pfst(p)], g[psnd(p)])), by=[oprod_map.defn])
    l.unfold(is_similarity)
    l.unfold(is_order_embedding)
    l.unfold(bij_on)
    l.split()
    l.split()
    l.unfold(maps_to)
    p0 = l.fix()
    l.intro()
    l.auto(
        by=[
            elem_prod_iff(A, B, p0),
            pair_elem_prod(f[pfst(p0)], g[psnd(p0)], A2, B2),
            maps_to.defn(f, A, A2),
            maps_to.defn(g, B, B2),
        ]
    )
    # Second coordinates are compared, then first ones; g preserves ≠ on B.
    p1, q1 = l.fixes()
    l.intros()
    l.auto(
        by=[
            elem_prod_iff(A, B, p1),
            elem_prod_iff(A, B, q1),
            oprod_rel_pair(R, S, pfst(p1), psnd(p1), pfst(q1), psnd(q1)),
            oprod_rel_pair(R2, S2, f[pfst(p1)], g[psnd(p1)], f[pfst(q1)], g[psnd(q1)]),
            inj_on.defn(g, B),
        ]
    )
    l.split()
    l.unfold(maps_to)
    p2 = l.fix()
    l.intro()
    l.auto(
        by=[
            elem_prod_iff(A, B, p2),
            pair_elem_prod(f[pfst(p2)], g[psnd(p2)], A2, B2),
            maps_to.defn(f, A, A2),
            maps_to.defn(g, B, B2),
        ]
    )
    l.unfold(inj_on)
    p3, q3 = l.fixes()
    l.intros()
    l.auto(
        by=[
            elem_prod_iff(A, B, p3),
            elem_prod_iff(A, B, q3),
            zf.pair_inj,
            bij_on.defn(f, A, A2),
            inj_on.defn(f, A),
            inj_on.defn(g, B),
        ]
    )
    # (y, z) ∈ A' × B' is (f x, g w).
    l.unfold(surj_on)
    y0 = l.fix()
    l.intro()
    l.have(
        And(elem(pfst(y0), A2), elem(psnd(y0), B2), y0 == pair(pfst(y0), psnd(y0))),
        by=[elem_prod_iff(A2, B2, y0)],
    )
    l.have(
        Exists(x, And(elem(x, A), f[x] == pfst(y0))),
        by=[bij_on.defn(f, A, A2), surj_on.defn(f, A, A2)],
    )
    x0, _ = l.obtain(-1)
    l.have(
        Exists(x, And(elem(x, B), g[x] == psnd(y0))),
        by=[bij_on.defn(g, B, B2), surj_on.defn(g, B, B2)],
    )
    w0, _ = l.obtain(-1)
    l.exists(pair(x0, w0))
    l.auto(by=[pair_elem_prod(x0, w0, A, B), pfst_pair, psnd_pair])


@Theorem(
    ForAll(
        [R, A, R2, A2, S, B, S2, B2],
        similar(R, A, R2, A2),
        similar(S, B, S2, B2),
        similar(oprod_rel(R, S), prod(A, B), oprod_rel(R2, S2), prod(A2, B2)),
    )
)
def similar_oprod(l):
    R, A, R2, A2, S, B, S2, B2 = l.fixes()
    l.intros()
    l.unfold(similar, at=0)
    l.unfold(similar, at=1)
    f0, _ = l.obtain(0)
    g0, _ = l.obtain(1)
    l.unfold(similar)
    l.exists(oprod_map(f0, g0))
    l.auto(by=[similarity_oprod(f0, g0, R, A, R2, A2, S, B, S2, B2)])


# (a, (b, 0)) ↦ ((a, b), 0) and (a, (c, 1)) ↦ ((a, c), 1).
odist_map = define_const(
    "odist_map",
    Lambda(
        p,
        If(
            psnd(p) == inl(pfst(psnd(p))),
            inl(pair(pfst(p), pfst(psnd(p)))),
            inr(pair(pfst(p), pfst(psnd(p)))),
        ),
    ),
)


@Theorem(
    ForAll(
        [a, b],
        And(
            Select(odist_map, pair(a, inl(b))) == inl(pair(a, b)),
            Select(odist_map, pair(a, inr(b))) == inr(pair(a, b)),
        ),
    )
)
def odist_map_apply(l):
    l.fixes()
    l.unfold(odist_map)
    l.simp()
    l.auto(by=[pfst_pair, psnd_pair, zf.pair_inj, zero_ne_one])


T = Consts("T", ArraySort(ZFSet, ZFSet, BoolSort()))[0]
C = Consts("C", ZFSet)[0]


@Theorem(
    ForAll(
        [R, S, T, A, B, C],
        is_similarity(
            odist_map,
            oprod_rel(R, osum_rel(S, T)),
            prod(A, osum_set(B, C)),
            osum_rel(oprod_rel(R, S), oprod_rel(R, T)),
            osum_set(prod(A, B), prod(A, C)),
        ),
    )
)
def similarity_odist(l):
    """Halmos: the ordinal product distributes over the ordinal sum on the left,
    up to similarity."""
    R, S, T, A, B, C = l.fixes()
    X, Y = prod(A, osum_set(B, C)), osum_set(prod(A, B), prod(A, C))
    tags = [zf.pair_inj, zero_ne_one, pfst_pair, psnd_pair]
    # Elements of A × (B ⊕ C) are (a, (b, 0)) and (a, (c, 1)).
    l.have(
        ForAll(
            p,
            elem(p, X),
            And(
                elem(pfst(p), A),
                Or(
                    And(
                        elem(pfst(psnd(p)), B),
                        p == pair(pfst(p), inl(pfst(psnd(p)))),
                    ),
                    And(
                        elem(pfst(psnd(p)), C),
                        p == pair(pfst(p), inr(pfst(psnd(p)))),
                    ),
                ),
            ),
        ),
        by=[elem_prod_iff, elem_osum_set],
    )
    l.have(
        ForAll([a, b], elem(a, A), elem(b, B), elem(inl(pair(a, b)), Y)),
        by=[elem_osum_set, pair_elem_prod] + tags,
    )
    l.have(
        ForAll([a, b], elem(a, A), elem(b, C), elem(inr(pair(a, b)), Y)),
        by=[elem_osum_set, pair_elem_prod] + tags,
    )

    def at(p):
        return odist_map_apply(pfst(p), pfst(psnd(p)))

    l.unfold(is_similarity)
    l.unfold(is_order_embedding)
    l.unfold(bij_on)
    l.split()
    l.split()
    l.unfold(maps_to)
    p0 = l.fix()
    l.intro()
    l.auto(by=[at(p0)])
    # Compare part by part, then by second coordinates, then by first ones.
    p1, q1 = l.fixes()
    l.intros()
    l.auto(by=[at(p1), at(q1), oprod_rel_pair] + osum_rel_pairs + tags)
    l.split()
    l.unfold(maps_to)
    p2 = l.fix()
    l.intro()
    l.auto(by=[at(p2)])
    l.unfold(inj_on)
    p3, q3 = l.fixes()
    l.intros()
    l.auto(by=[at(p3), at(q3)] + tags)
    # Each ((a, b), 0) and ((a, c), 1) is hit.
    l.unfold(surj_on)
    y0 = l.fix()
    l.intro()
    y1 = pfst(y0)
    l.have(
        Or(
            And(
                elem(pfst(y1), A),
                elem(psnd(y1), B),
                y0 == inl(pair(pfst(y1), psnd(y1))),
            ),
            And(
                elem(pfst(y1), A),
                elem(psnd(y1), C),
                y0 == inr(pair(pfst(y1), psnd(y1))),
            ),
        ),
        by=[
            elem_osum_set(prod(A, B), prod(A, C), y0),
            elem_prod_iff(A, B, y1),
            elem_prod_iff(A, C, y1),
        ],
    )
    l.cases(
        And(elem(pfst(y1), A), elem(psnd(y1), B), y0 == inl(pair(pfst(y1), psnd(y1)))),
        And(elem(pfst(y1), A), elem(psnd(y1), C), y0 == inr(pair(pfst(y1), psnd(y1)))),
    )
    l.exists(pair(pfst(y1), inl(psnd(y1))))
    l.auto(
        by=[
            odist_map_apply(pfst(y1), psnd(y1)),
            pair_elem_prod(pfst(y1), inl(psnd(y1)), A, osum_set(B, C)),
            elem_osum_set(B, C, inl(psnd(y1))),
        ]
        + tags
    )
    l.exists(pair(pfst(y1), inr(psnd(y1))))
    l.auto(
        by=[
            odist_map_apply(pfst(y1), psnd(y1)),
            pair_elem_prod(pfst(y1), inr(psnd(y1)), A, osum_set(B, C)),
            elem_osum_set(B, C, inr(psnd(y1))),
        ]
        + tags
    )


# ((a, b), c) ↦ (a, (b, c))
oprod_assoc_map = define_const(
    "oprod_assoc_map", Lambda(p, pair(pfst(pfst(p)), pair(psnd(pfst(p)), psnd(p))))
)


@Theorem(
    ForAll(
        [a, b, c],
        Select(oprod_assoc_map, pair(pair(a, b), c)) == pair(a, pair(b, c)),
    )
)
def oprod_assoc_map_apply(l):
    l.fixes()
    l.unfold(oprod_assoc_map)
    l.simp()
    l.auto(by=[pfst_pair, psnd_pair])


@Theorem(
    ForAll(
        [R, S, T, A, B, C],
        is_similarity(
            oprod_assoc_map,
            oprod_rel(oprod_rel(R, S), T),
            prod(prod(A, B), C),
            oprod_rel(R, oprod_rel(S, T)),
            prod(A, prod(B, C)),
        ),
    )
)
def similarity_oprod_assoc(l):
    """Halmos: the ordinal product is associative up to similarity."""
    R, S, T, A, B, C = l.fixes()
    X, Y = prod(prod(A, B), C), prod(A, prod(B, C))
    # Elements of (A × B) × C are ((a, b), c).
    l.have(
        ForAll(
            p,
            elem(p, X),
            And(
                elem(pfst(pfst(p)), A),
                elem(psnd(pfst(p)), B),
                elem(psnd(p), C),
                p == pair(pair(pfst(pfst(p)), psnd(pfst(p))), psnd(p)),
            ),
        ),
        by=[elem_prod_iff],
    )
    l.have(
        ForAll(
            [a, b, c],
            elem(a, A),
            elem(b, B),
            elem(c, C),
            elem(pair(a, pair(b, c)), Y),
        ),
        by=[pair_elem_prod],
    )

    def at(p):
        return oprod_assoc_map_apply(pfst(pfst(p)), psnd(pfst(p)), psnd(p))

    def rel(p, q):
        a, b, c = pfst(pfst(p)), psnd(pfst(p)), psnd(p)
        a1, b1, c1 = pfst(pfst(q)), psnd(pfst(q)), psnd(q)
        return [
            oprod_rel_pair(oprod_rel(R, S), T, pair(a, b), c, pair(a1, b1), c1),
            oprod_rel_pair(R, S, a, b, a1, b1),
            oprod_rel_pair(R, oprod_rel(S, T), a, pair(b, c), a1, pair(b1, c1)),
            oprod_rel_pair(S, T, b, c, b1, c1),
        ]

    l.unfold(is_similarity)
    l.unfold(is_order_embedding)
    l.unfold(bij_on)
    l.split()
    l.split()
    l.unfold(maps_to)
    p0 = l.fix()
    l.intro()
    l.auto(by=[at(p0)])
    # Both orders compare c, then b, then a.
    p1, q1 = l.fixes()
    l.intros()
    l.auto(by=[at(p1), at(q1), zf.pair_inj] + rel(p1, q1))
    l.split()
    l.unfold(maps_to)
    p2 = l.fix()
    l.intro()
    l.auto(by=[at(p2)])
    l.unfold(inj_on)
    p3, q3 = l.fixes()
    l.intros()
    l.auto(by=[at(p3), at(q3), zf.pair_inj])
    l.unfold(surj_on)
    y0 = l.fix()
    l.intro()
    a0, z0 = pfst(y0), psnd(y0)
    b0, c0 = pfst(z0), psnd(z0)
    l.have(
        And(elem(a0, A), elem(b0, B), elem(c0, C), y0 == pair(a0, pair(b0, c0))),
        by=[elem_prod_iff(A, prod(B, C), y0), elem_prod_iff(B, C, z0)],
    )
    l.exists(pair(pair(a0, b0), c0))
    l.auto(
        by=[
            oprod_assoc_map_apply(a0, b0, c0),
            pair_elem_prod(a0, b0, A, B),
            pair_elem_prod(pair(a0, b0), c0, prod(A, B), C),
        ]
    )


@Theorem(
    ForAll(
        [A, B, C],
        is_ordinal(A),
        is_ordinal(B),
        is_ordinal(C),
        omul(A, oadd(B, C)) == oadd(omul(A, B), omul(A, C)),
    )
)
def omul_oadd(l):
    """Halmos: α(β + γ) = αβ + αγ."""
    A, B, C = l.fixes()
    l.intros()
    BC, AB, AC = oadd(B, C), omul(A, B), omul(A, C)
    le_ = nat_le_rel
    l.have(
        And(is_ordinal(BC), similar(le_, BC, oplus, osum_set(B, C))),
        by=[oadd_spec(B, C)],
    )
    l.have(
        And(is_ordinal(AB), similar(le_, AB, otimes, prod(A, B))), by=[omul_spec(A, B)]
    )
    l.have(
        And(is_ordinal(AC), similar(le_, AC, otimes, prod(A, C))), by=[omul_spec(A, C)]
    )
    D = oadd(AB, AC)
    l.have(
        And(is_ordinal(D), similar(le_, D, oplus, osum_set(AB, AC))),
        by=[oadd_spec(AB, AC)],
    )
    # α × (β + γ) ≅ α × (β ⊕ γ) ≅ (α × β) ⊕ (α × γ) ≅ αβ ⊕ αγ ≅ αβ + αγ.
    X1 = prod(A, BC)
    X2 = prod(A, osum_set(B, C))
    X3 = osum_set(prod(A, B), prod(A, C))
    X4 = osum_set(AB, AC)
    R2 = oprod_rel(le_, oplus)
    R3 = osum_rel(otimes, otimes)
    l.have(
        similar(otimes, X1, R2, X2),
        by=[
            similar_oprod(le_, A, le_, A, le_, BC, oplus, osum_set(B, C)),
            similar_refl(le_, A),
        ],
    )
    l.have(
        similar(R2, X2, R3, X3),
        by=[similar.defn(R2, X2, R3, X3), similarity_odist(le_, le_, le_, A, B, C)],
    )
    l.have(
        similar(R3, X3, oplus, X4),
        by=[
            similar_osum(otimes, prod(A, B), le_, AB, otimes, prod(A, C), le_, AC),
            similar_symm(le_, AB, otimes, prod(A, B)),
            similar_symm(le_, AC, otimes, prod(A, C)),
        ],
    )
    l.have(similar(oplus, X4, le_, D), by=[similar_symm(le_, D, oplus, X4)])
    l.have(similar(otimes, X1, R3, X3), by=[similar_trans(otimes, X1, R2, X2, R3, X3)])
    l.have(
        similar(otimes, X1, oplus, X4),
        by=[similar_trans(otimes, X1, R3, X3, oplus, X4)],
    )
    l.have(
        similar(otimes, X1, le_, D), by=[similar_trans(otimes, X1, oplus, X4, le_, D)]
    )
    l.auto(by=[omul.defn(A, BC), ord_of_eq(otimes, X1, D)])


@Theorem(
    ForAll(
        [A, B, C],
        is_ordinal(A),
        is_ordinal(B),
        is_ordinal(C),
        omul(omul(A, B), C) == omul(A, omul(B, C)),
    )
)
def omul_assoc(l):
    """Halmos: (αβ)γ = α(βγ)."""
    A, B, C = l.fixes()
    l.intros()
    AB, BC = omul(A, B), omul(B, C)
    le_ = nat_le_rel
    l.have(
        And(is_ordinal(AB), similar(le_, AB, otimes, prod(A, B))), by=[omul_spec(A, B)]
    )
    l.have(
        And(is_ordinal(BC), similar(le_, BC, otimes, prod(B, C))), by=[omul_spec(B, C)]
    )
    D = omul(A, BC)
    l.have(
        And(is_ordinal(D), similar(le_, D, otimes, prod(A, BC))), by=[omul_spec(A, BC)]
    )
    # αβ × γ ≅ (α × β) × γ ≅ α × (β × γ) ≅ α × βγ ≅ α(βγ).
    X1 = prod(AB, C)
    X2 = prod(prod(A, B), C)
    X3 = prod(A, prod(B, C))
    X4 = prod(A, BC)
    R2 = oprod_rel(otimes, le_)
    R3 = oprod_rel(le_, otimes)
    l.have(
        similar(otimes, X1, R2, X2),
        by=[
            similar_oprod(le_, AB, otimes, prod(A, B), le_, C, le_, C),
            similar_refl(le_, C),
        ],
    )
    l.have(
        similar(R2, X2, R3, X3),
        by=[
            similar.defn(R2, X2, R3, X3),
            similarity_oprod_assoc(le_, le_, le_, A, B, C),
        ],
    )
    l.have(
        similar(R3, X3, otimes, X4),
        by=[
            similar_oprod(le_, A, le_, A, otimes, prod(B, C), le_, BC),
            similar_refl(le_, A),
            similar_symm(le_, BC, otimes, prod(B, C)),
        ],
    )
    l.have(similar(otimes, X4, le_, D), by=[similar_symm(le_, D, otimes, X4)])
    l.have(similar(otimes, X1, R3, X3), by=[similar_trans(otimes, X1, R2, X2, R3, X3)])
    l.have(
        similar(otimes, X1, otimes, X4),
        by=[similar_trans(otimes, X1, R3, X3, otimes, X4)],
    )
    l.have(
        similar(otimes, X1, le_, D), by=[similar_trans(otimes, X1, otimes, X4, le_, D)]
    )
    l.auto(by=[omul.defn(AB, C), ord_of_eq(otimes, X1, D)])


# Halmos: 2ω = ω but ω2 = ω + ω ≠ ω, so multiplication is not commutative.


@Theorem(omul(two, omega) == omega)
def two_omul_omega(l):
    """Halmos: 2ω = ω, by (a, n) ↦ 2n + a."""
    X = prod(two, omega)
    F = Lambda(p, bit(pfst(p), psnd(p)))
    # Elements of 2 × ω are (a, n) with a ∈ {0, 1} and n ∈ ω.
    l.have(
        ForAll(
            p,
            elem(p, X),
            And(
                Or(pfst(p) == zero, pfst(p) == one),
                elem(psnd(p), omega),
                p == pair(pfst(p), psnd(p)),
            ),
        ),
        by=[elem_prod_iff, elem_two],
    )
    l.have(
        ForAll(n, elem(n, omega), elem(bit(zero, n), bit(one, n))),
        by=[bit.defn, elem_succ_self, zero_ne_one],
    )
    l.have(is_similarity(F, otimes, X, nat_le_rel, omega))
    l.unfold(is_similarity)
    l.unfold(is_order_embedding)
    l.unfold(bij_on)
    l.split()
    l.split()
    l.unfold(maps_to)
    p0 = l.fix()
    l.intro()
    l.simp()
    l.auto(by=[bit_elem_omega(pfst(p0), psnd(p0))])
    # Compare n and m first; when they agree, 2n ≤ 2n + 1.
    p1, q1 = l.fixes()
    l.intros()
    l.simp()
    n1, m1 = psnd(p1), psnd(q1)
    a1, b1 = pfst(p1), pfst(q1)
    l.auto(
        by=[
            oprod_rel_pair(nat_le_rel, nat_le_rel, a1, n1, b1, m1),
            nat_le.defn,
            nat_comparable(n1, m1),
            comparable.defn(n1, m1),
            nat_elem_asymm(n1, m1),
            bit_elem_bit(a1, b1, n1, m1),
            bit_elem_bit(b1, a1, m1, n1),
            bit_elem_omega(a1, n1),
            bit_elem_omega(b1, m1),
            nat_elem_asymm(bit(a1, n1), bit(b1, m1)),
            nat_elem_asymm(bit(b1, m1), bit(a1, n1)),
            nat_not_elem_self(bit(a1, n1)),
            elem_one(zero),
            zf.elem_emp(one),
            zero.defn,
            zero_ne_one,
        ]
    )
    l.split()
    l.unfold(maps_to)
    p2 = l.fix()
    l.intro()
    l.simp()
    l.auto(by=[bit_elem_omega(pfst(p2), psnd(p2))])
    # Different pairs have different values, as the values are ordered like the pairs.
    l.unfold(inj_on)
    p3, q3 = l.fixes()
    l.intros()
    l.simp(at=-1)
    n3, m3 = psnd(p3), psnd(q3)
    a3, b3 = pfst(p3), pfst(q3)
    l.auto(
        by=[
            nat_comparable(n3, m3),
            comparable.defn(n3, m3),
            bit_elem_bit(a3, b3, n3, m3),
            bit_elem_bit(b3, a3, m3, n3),
            bit_elem_omega(a3, n3),
            nat_not_elem_self(bit(a3, n3)),
        ]
    )
    # Every natural number is 2n or 2n + 1.
    l.unfold(surj_on)
    k0 = l.fix()
    l.intro()
    l.have(
        Exists(n, And(elem(n, omega), Or(k0 == bit(zero, n), k0 == bit(one, n)))),
        by=[exists_bit(k0)],
    )
    n4, _ = l.obtain(-1)
    l.cases(k0 == bit(zero, n4), k0 == bit(one, n4))
    l.exists(pair(zero, n4))
    l.simp()
    l.auto(by=[pair_elem_prod(zero, n4, two, omega), elem_two, pfst_pair, psnd_pair])
    l.exists(pair(one, n4))
    l.simp()
    l.auto(by=[pair_elem_prod(one, n4, two, omega), elem_two, pfst_pair, psnd_pair])
    l.unfold(omul)
    l.auto(
        by=[
            ord_of_eq(otimes, X, omega),
            similar.defn(otimes, X, nat_le_rel, omega),
            omega_is_ordinal,
        ]
    )


@Theorem(
    is_similarity(
        Lambda(x, inl(x)),
        nat_le_rel,
        omega,
        oplus,
        seg(oplus, osum_set(omega, omega), inr(zero)),
    )
)
def similarity_seg_inr_zero(l):
    """In ω ⊕ ω the elements before (0, 1) are the (n, 0), a copy of ω."""
    Y = osum_set(omega, omega)
    top = inr(zero)
    S = seg(oplus, Y, top)
    hyps = [
        ForAll(y, elem(y, S) == And(elem(y, Y), oplus[y, top], y != top)),
        ForAll(x, elem(x, omega), elem(inl(x), Y)),
        ForAll(x, inl(x) != top),
    ]
    l.have(hyps[0], by=[elem_seg_iff])
    l.have(hyps[1], by=[elem_osum_set, pfst_pair])
    l.have(hyps[2], by=[zf.pair_inj, zero_ne_one])
    l.unfold(is_similarity)
    l.unfold(is_order_embedding)
    l.unfold(bij_on)
    l.split()
    l.split()
    l.unfold(maps_to)
    l.fix()
    l.intro()
    l.simp()
    l.auto(by=[osum_rel_inl_inr])
    l.fixes()
    l.intros()
    l.simp()
    l.auto(by=[osum_rel_inl_inl])
    l.split()
    l.unfold(maps_to)
    l.fix()
    l.intro()
    l.simp()
    l.auto(by=[osum_rel_inl_inr])
    l.unfold(inj_on)
    l.fixes()
    l.intros()
    l.simp(at=-1)
    l.auto(by=[zf.pair_inj])
    # An element (x, 1) before (0, 1) would have x < 0.
    l.unfold(surj_on)
    y0 = l.fix()
    l.intro()
    x0 = pfst(y0)
    l.have(
        And(elem(y0, Y), oplus[y0, top], y0 != top),
        by=[elem_seg_iff(oplus, Y, top, y0)],
    )
    for h in hyps:
        l.clear(h)
    l.have(
        Or(
            And(elem(x0, omega), y0 == inl(x0)),
            And(elem(x0, omega), y0 == inr(x0)),
        ),
        by=[elem_osum_set(omega, omega, y0)],
    )
    l.have(y0 == inl(x0))
    l.auto(
        by=[
            osum_rel_inr_inr(nat_le_rel, nat_le_rel, x0, zero),
            nat_le.defn,
            zero.defn,
            zf.elem_emp(x0),
        ]
    )
    l.exists(x0)
    l.simp()
    l.auto()


@Theorem(oadd(omega, omega) != omega)
def oadd_omega_omega_ne(l):
    """Halmos: ω + ω ≠ ω. Otherwise a similarity h of ω ⊕ ω onto ω carries the
    copy of ω before (0, 1) onto the initial segment of ω before h(0, 1), a
    natural number, and a well ordered set is not similar to an initial segment."""
    l.intro()
    Y = osum_set(omega, omega)
    top = inr(zero)
    l.have(
        similar(oplus, Y, nat_le_rel, omega),
        by=[
            oadd_spec(omega, omega),
            omega_is_ordinal,
            similar_symm(nat_le_rel, oadd(omega, omega), oplus, Y),
        ],
    )
    l.unfold(similar, at=-1)
    h, _ = l.obtain(-1)
    l.have(elem(top, Y), by=[elem_osum_set(omega, omega, top), pfst_pair, omega_zero])
    n0 = h[top]
    l.have(
        elem(n0, omega),
        by=[
            is_similarity.defn(h, oplus, Y, nat_le_rel, omega),
            is_order_embedding.defn(h, oplus, Y, nat_le_rel, omega),
            maps_to.defn(h, Y, omega),
        ],
    )
    S = seg(oplus, Y, top)
    l.have(
        is_similarity(h, oplus, S, nat_le_rel, seg(nat_le_rel, omega, n0)),
        by=[similarity_seg(h, oplus, Y, nat_le_rel, omega, top)],
    )
    g = Lambda(x, inl(x))
    l.have(
        is_similarity(
            Lambda(x, h[g[x]]),
            nat_le_rel,
            omega,
            nat_le_rel,
            seg(nat_le_rel, omega, n0),
        ),
        by=[
            similarity_seg_inr_zero,
            similarity_comp(
                g,
                h,
                nat_le_rel,
                omega,
                oplus,
                S,
                nat_le_rel,
                seg(nat_le_rel, omega, n0),
            ),
        ],
    )
    l.auto(
        by=[
            not_similarity_seg(Lambda(x, h[g[x]]), nat_le_rel, omega, n0),
            omega_well_order,
        ]
    )


# Halmos: ω2 = ω + ω ≠ ω = 2ω.
omul_not_comm = prove(
    omul(omega, two) != omul(two, omega),
    by=[omul_two(omega), omega_is_ordinal, two_omul_omega, oadd_omega_omega_ne],
)
