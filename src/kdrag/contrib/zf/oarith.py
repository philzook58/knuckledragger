"""
Ordinal arithmetic (Halmos §21).

The ordinal sum of well ordered sets A and B tags the elements of A with 0
and those of B with 1, keeps each order, and puts every element of A before
every element of B. α + β is the ordinal of the ordinal sum, via the counting
theorem. The sum's order is a named relation `osum_rel` rather than a lambda,
which avoids the solver problems recorded in the issue tracker.
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
    Not,
    Or,
    Select,
)
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import ZFSet, elem, le, pair, sep, succ, zero
from kdrag.contrib.zf.count import counting_theorem, ord_of, ord_of_eq
from kdrag.contrib.zf.fun import (
    bij_on,
    inj_on,
    maps_to,
    pfst,
    pfst_pair,
    surj_on,
)
from kdrag.contrib.zf.nat import (
    elem_one,
    elem_succ,
    elem_succ_self,
    exists_eq_succ_of_ne_zero,
    is_transitive,
    nat_is_transitive,
    omega,
    omega_succ,
    omega_zero,
    one,
    succ_inj,
    succ_ne_zero,
    zero_ne_one,
)
from kdrag.contrib.zf.order import comparable, comparable_zero, nat_le, succ_elem_succ
from kdrag.contrib.zf.ordinal import is_ordinal, is_ordinal_succ, omega_is_ordinal
from kdrag.contrib.zf.ordset import (
    ordinal_le_of_elem,
    ordinal_not_elem_self,
    ordinal_well_order,
)
from kdrag.contrib.zf.poset import (
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
    is_order_embedding,
    is_similarity,
    similar,
    similar_refl,
    similar_symm,
    similar_trans,
)
from kdrag.contrib.zf.dsum import elem_osum_set, inl, inr, osum_set

A, B, E, a, b, p, q, r, x, y = Consts("A B E a b p q r x y", ZFSet)
A2, B2 = Consts("A2 B2", ZFSet)
R, S, R2, S2 = Consts("R S R2 S2", ArraySort(ZFSet, ZFSet, BoolSort()))
f, g = Consts("f g", ArraySort(ZFSet, ZFSet))

osum_le = define(
    "osum_le",
    [R, S, p, q],
    Or(
        And(p == pair(pfst(p), zero), q == pair(pfst(q), zero), R[pfst(p), pfst(q)]),
        And(p == pair(pfst(p), one), q == pair(pfst(q), one), S[pfst(p), pfst(q)]),
        And(p == pair(pfst(p), zero), q == pair(pfst(q), one)),
    ),
)
osum_rel = define("osum_rel", [R, S], Lambda([p, q], osum_le(R, S, p, q)))


@Theorem(ForAll([R, S, p, q], osum_rel(R, S)[p, q] == osum_le(R, S, p, q)))
def osum_rel_apply(l):
    l.fixes()
    l.unfold(osum_rel)
    l.simp()
    l.auto()


@Theorem(
    ForAll(
        [R, S, A, B],
        is_partial_order(R, A),
        is_partial_order(S, B),
        is_partial_order(osum_rel(R, S), osum_set(A, B)),
    )
)
def osum_partial_order(l):
    """The ordinal sum order is a partial order: compare within A, within B, and
    put A before B."""
    R, S, A, B = l.fixes()
    l.intros()
    tags = [zf.pair_inj, zero_ne_one]
    l.unfold(is_partial_order)
    l.split()
    p0 = l.fix()
    l.intro()
    l.auto(
        by=[
            elem_osum_set(A, B, p0),
            osum_rel_apply(R, S, p0, p0),
            osum_le.defn(R, S, p0, p0),
            partial_order_refl(R, A, pfst(p0)),
            partial_order_refl(S, B, pfst(p0)),
        ]
    )
    p1, q1 = l.fixes()
    l.intros()
    l.auto(
        by=[
            elem_osum_set(A, B, p1),
            elem_osum_set(A, B, q1),
            osum_rel_apply(R, S, p1, q1),
            osum_rel_apply(R, S, q1, p1),
            osum_le.defn(R, S, p1, q1),
            osum_le.defn(R, S, q1, p1),
            partial_order_antisymm(R, A, pfst(p1), pfst(q1)),
            partial_order_antisymm(S, B, pfst(p1), pfst(q1)),
        ]
        + tags
    )
    p2, q2, r2 = l.fixes()
    l.intros()
    l.auto(
        by=[
            elem_osum_set(A, B, p2),
            elem_osum_set(A, B, q2),
            elem_osum_set(A, B, r2),
            osum_rel_apply(R, S, p2, q2),
            osum_rel_apply(R, S, q2, r2),
            osum_rel_apply(R, S, p2, r2),
            osum_le.defn(R, S, p2, q2),
            osum_le.defn(R, S, q2, r2),
            osum_le.defn(R, S, p2, r2),
            partial_order_trans(R, A, pfst(p2), pfst(q2), pfst(r2)),
            partial_order_trans(S, B, pfst(p2), pfst(q2), pfst(r2)),
        ]
        + tags
    )


# The parts of E ⊆ A ⊕ B coming from A and from B, named to keep lambdas out
# of later goals.
left_part = define("left_part", [E, A], sep(A, Lambda(x, elem(pair(x, zero), E))))
right_part = define("right_part", [E, B], sep(B, Lambda(x, elem(pair(x, one), E))))


@Theorem(
    ForAll(
        [E, A, x], elem(x, left_part(E, A)) == And(elem(x, A), elem(pair(x, zero), E))
    )
)
def elem_left_part(l):
    l.fixes()
    l.unfold(left_part)
    l.rw(zf.elem_sep)
    l.simp()
    l.auto()


@Theorem(
    ForAll(
        [E, B, x], elem(x, right_part(E, B)) == And(elem(x, B), elem(pair(x, one), E))
    )
)
def elem_right_part(l):
    l.fixes()
    l.unfold(right_part)
    l.rw(zf.elem_sep)
    l.simp()
    l.auto()


@Theorem(
    ForAll(
        [R, S, A, B],
        is_well_order(R, A),
        is_well_order(S, B),
        is_well_order(osum_rel(R, S), osum_set(A, B)),
    )
)
def osum_well_order(l):
    """Halmos: the ordinal sum of well ordered sets is well ordered."""
    R, S, A, B = l.fixes()
    l.intros()
    X = osum_set(A, B)
    l.unfold(is_well_order)
    l.split()
    l.auto(
        by=[
            osum_partial_order(R, S, A, B),
            partial_order_of_well_order(R, A),
            partial_order_of_well_order(S, B),
        ]
    )
    E0 = l.fix()
    l.intros()
    L, Rt = left_part(E0, A), right_part(E0, B)
    tags = [zf.pair_inj, zero_ne_one, pfst_pair]
    l.cases(L != zf.emp, L == zf.emp)
    # Some element of E comes from A: the least such one is least in E.
    l.have(L <= A, by=[le.defn, elem_left_part])
    l.have(Exists(a, is_least(R, L, a)), by=[exists_least(R, A, L)])
    a0, _ = l.obtain(-1)
    l.exists(pair(a0, zero))
    l.unfold(is_least)
    l.split()
    l.auto(by=[is_least.defn(R, L, a0), elem_left_part(E0, A, a0)])
    q0 = l.fix()
    l.intro()
    l.auto(
        by=[
            le.defn(E0, X),
            elem_osum_set(A, B, q0),
            is_least.defn(R, L, a0),
            elem_left_part(E0, A, pfst(q0)),
            osum_rel_apply(R, S, pair(a0, zero), q0),
            osum_le.defn(R, S, pair(a0, zero), q0),
        ]
        + tags
    )
    # Otherwise all of E comes from B, and the least element of that part is least.
    l.have(ForAll(q, elem(q, E0), q == pair(pfst(q), one)))
    q1 = l.fix()
    l.intro()
    l.auto(
        by=[
            le.defn(E0, X),
            elem_osum_set(A, B, q1),
            elem_left_part(E0, A, pfst(q1)),
            zf.elem_emp(pfst(q1)),
        ]
    )
    l.have(Exists(q, elem(q, E0)), by=[zf.not_emp_exists_elem(E0)])
    e0, _ = l.obtain(-1)
    l.have(
        elem(pfst(e0), Rt),
        by=[
            elem_right_part(E0, B, pfst(e0)),
            le.defn(E0, X),
            elem_osum_set(A, B, e0),
            zf.pair_inj,
            zero_ne_one,
        ],
    )
    l.have(Rt <= B, by=[le.defn, elem_right_part])
    l.have(Rt != zf.emp, by=[zf.elem_emp(pfst(e0))])
    l.have(Exists(b, is_least(S, Rt, b)), by=[exists_least(S, B, Rt)])
    b0, _ = l.obtain(-1)
    l.exists(pair(b0, one))
    l.unfold(is_least)
    l.split()
    l.auto(by=[is_least.defn(S, Rt, b0), elem_right_part(E0, B, b0)])
    q2 = l.fix()
    l.intro()
    l.auto(
        by=[
            le.defn(E0, X),
            elem_osum_set(A, B, q2),
            is_least.defn(S, Rt, b0),
            elem_right_part(E0, B, pfst(q2)),
            osum_rel_apply(R, S, pair(b0, one), q2),
            osum_le.defn(R, S, pair(b0, one), q2),
        ]
        + tags
    )


# The order of the sum on tagged elements, as in Mathlib's Sum.lex_inl_inl etc.
_tags = [osum_rel_apply, osum_le.defn, pfst_pair, zf.pair_inj, zero_ne_one]
osum_rel_inl_inl = prove(
    ForAll([R, S, x, y], osum_rel(R, S)[inl(x), inl(y)] == R[x, y]), by=_tags
)
osum_rel_inr_inr = prove(
    ForAll([R, S, x, y], osum_rel(R, S)[inr(x), inr(y)] == S[x, y]), by=_tags
)
osum_rel_inl_inr = prove(ForAll([R, S, x, y], osum_rel(R, S)[inl(x), inr(y)]), by=_tags)
not_osum_rel_inr_inl = prove(
    ForAll([R, S, x, y], Not(osum_rel(R, S)[inr(x), inl(y)])), by=_tags
)
osum_rel_pairs = [
    osum_rel_inl_inl,
    osum_rel_inr_inr,
    osum_rel_inl_inr,
    not_osum_rel_inr_inl,
]

# Similarities f: A → A' and g: B → B' act on the two parts of A ⊕ B.
osum_map = define(
    "osum_map",
    [f, g],
    Lambda(p, If(p == inl(pfst(p)), inl(f[pfst(p)]), inr(g[pfst(p)]))),
)


@Theorem(
    ForAll(
        [f, g, x],
        And(osum_map(f, g)[inl(x)] == inl(f[x]), osum_map(f, g)[inr(x)] == inr(g[x])),
    )
)
def osum_map_apply(l):
    l.fixes()
    l.unfold(osum_map)
    l.simp()
    l.auto(by=[pfst_pair, zf.pair_inj, zero_ne_one])


@Theorem(
    ForAll(
        [f, g, R, A, R2, A2, S, B, S2, B2],
        is_similarity(f, R, A, R2, A2),
        is_similarity(g, S, B, S2, B2),
        is_similarity(
            osum_map(f, g),
            osum_rel(R, S),
            osum_set(A, B),
            osum_rel(R2, S2),
            osum_set(A2, B2),
        ),
    )
)
def similarity_osum(l):
    """Halmos: similar summands have similar ordinal sums."""
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
    X, X2 = osum_set(A, B), osum_set(A2, B2)
    # Each element of A ⊕ B is inl a with a ∈ A or inr b with b ∈ B.
    l.have(
        ForAll(
            p,
            elem(p, X),
            Or(
                And(elem(pfst(p), A), p == inl(pfst(p))),
                And(elem(pfst(p), B), p == inr(pfst(p))),
            ),
        ),
        by=[elem_osum_set],
    )
    l.have(
        ForAll(x, elem(x, A), elem(inl(f[x]), X2)),
        by=[elem_osum_set, pfst_pair, bij_on.defn, maps_to.defn],
    )
    l.have(
        ForAll(x, elem(x, B), elem(inr(g[x]), X2)),
        by=[elem_osum_set, pfst_pair, bij_on.defn, maps_to.defn],
    )
    l.unfold(is_similarity)
    l.unfold(is_order_embedding)
    l.split()
    l.split()
    l.unfold(maps_to)
    p0 = l.fix()
    l.intro()
    l.auto(by=[osum_map_apply(f, g, pfst(p0))])
    # The order is compared part by part.
    p1, q1 = l.fixes()
    l.intros()
    l.auto(
        by=[osum_map_apply(f, g, pfst(p1)), osum_map_apply(f, g, pfst(q1))]
        + osum_rel_pairs
    )
    l.unfold(bij_on)
    l.split()
    l.unfold(maps_to)
    p2 = l.fix()
    l.intro()
    l.auto(by=[osum_map_apply(f, g, pfst(p2))])
    l.unfold(inj_on)
    p3, q3 = l.fixes()
    l.intros()
    l.auto(
        by=[
            osum_map_apply(f, g, pfst(p3)),
            osum_map_apply(f, g, pfst(q3)),
            zf.pair_inj,
            zero_ne_one,
            bij_on.defn,
            inj_on.defn,
        ]
    )
    # inl y with y ∈ A' is inl (f x), and likewise on the right.
    l.unfold(surj_on)
    y0 = l.fix()
    l.intro()
    l.have(
        Or(
            And(elem(pfst(y0), A2), y0 == inl(pfst(y0))),
            And(elem(pfst(y0), B2), y0 == inr(pfst(y0))),
        ),
        by=[elem_osum_set(A2, B2, y0)],
    )
    l.cases(
        And(elem(pfst(y0), A2), y0 == inl(pfst(y0))),
        And(elem(pfst(y0), B2), y0 == inr(pfst(y0))),
    )
    l.have(
        Exists(x, And(elem(x, A), f[x] == pfst(y0))),
        by=[bij_on.defn(f, A, A2), surj_on.defn(f, A, A2)],
    )
    x0, _ = l.obtain(-1)
    l.exists(inl(x0))
    l.auto(by=[osum_map_apply(f, g, x0), elem_osum_set(A, B, inl(x0)), pfst_pair])
    l.have(
        Exists(x, And(elem(x, B), g[x] == pfst(y0))),
        by=[bij_on.defn(g, B, B2), surj_on.defn(g, B, B2)],
    )
    x1, _ = l.obtain(-1)
    l.exists(inr(x1))
    l.auto(by=[osum_map_apply(f, g, x1), elem_osum_set(A, B, inr(x1)), pfst_pair])


# α + β is the ordinal number of the ordinal sum of α and β.
oplus = osum_rel(nat_le_rel, nat_le_rel)
oadd = define("oadd", [A, B], ord_of(oplus, osum_set(A, B)))


@Theorem(
    ForAll(
        [A, B, p, q],
        elem(p, osum_set(A, B)),
        elem(q, osum_set(A, B)),
        oplus[p, q]
        == Or(
            And(
                p == pair(pfst(p), zero),
                q == pair(pfst(q), zero),
                nat_le(pfst(p), pfst(q)),
            ),
            And(
                p == pair(pfst(p), one),
                q == pair(pfst(q), one),
                nat_le(pfst(p), pfst(q)),
            ),
            And(p == pair(pfst(p), zero), q == pair(pfst(q), one)),
        ),
    )
)
def oplus_apply(l):
    """The order of α ⊕ β spelled out with ≤ on ordinals."""
    A, B, p0, q0 = l.fixes()
    l.intros()
    l.rw(osum_rel_apply)
    l.unfold(osum_le)
    l.simp()
    l.auto(by=[nat_le.defn])


@Theorem(ForAll(A, is_ordinal(A), oadd(A, zero) == A))
def oadd_zero(l):
    """Halmos: α + 0 = α, by the similarity (x, 0) ↦ x."""
    A = l.fix()
    l.intro()
    X = osum_set(A, zero)
    f = Lambda(p, pfst(p))
    # Every element of α ⊕ 0 is (x, 0) with x ∈ α.
    l.have(
        ForAll(p, elem(p, X), And(elem(pfst(p), A), p == pair(pfst(p), zero))),
        by=[elem_osum_set, zero.defn, zf.elem_emp],
    )
    l.have(is_similarity(f, oplus, X, nat_le_rel, A))
    l.unfold(is_similarity)
    l.unfold(is_order_embedding)
    l.split()
    l.split()
    l.auto(by=[maps_to.defn(f, X, A)])
    p0, q0 = l.fixes()
    l.intros()
    l.simp()
    l.auto(by=[oplus_apply(A, zero, p0, q0), zero_ne_one, zf.pair_inj, nat_le.defn])
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
    l.auto(by=[elem_osum_set(A, zero, pair(x0, zero)), pfst_pair])
    l.unfold(oadd)
    l.auto(by=[ord_of_eq(oplus, X, A), similar.defn(oplus, X, nat_le_rel, A)])


@Theorem(ForAll(A, is_ordinal(A), oadd(A, one) == succ(A)))
def oadd_one(l):
    """Halmos: α + 1 = α⁺, by (x, 0) ↦ x and (0, 1) ↦ α."""
    A = l.fix()
    l.intro()
    X = osum_set(A, one)
    top = pair(zero, one)
    f = Lambda(p, If(p == top, A, pfst(p)))
    l.have(Not(elem(A, A)), by=[ordinal_not_elem_self(A, A)])
    l.have(ForAll(x, elem(x, A), x <= A), by=[ordinal_le_of_elem])
    # Elements of α ⊕ 1 are (x, 0) with x ∈ α, and (0, 1).
    l.have(
        ForAll(
            p,
            elem(p, X),
            Or(And(elem(pfst(p), A), p == pair(pfst(p), zero)), p == top),
        ),
        by=[elem_osum_set, elem_one],
    )
    l.have(ForAll(x, top != pair(x, zero)), by=[zf.pair_inj, zero_ne_one])
    l.have(is_similarity(f, oplus, X, nat_le_rel, succ(A)))
    l.unfold(is_similarity)
    l.unfold(is_order_embedding)
    l.split()
    l.split()
    l.unfold(maps_to)
    l.fix()
    l.intro()
    l.simp()
    l.auto(by=[elem_succ])
    # Within α the order is ≤; everything in α is below α; α is above nothing in α.
    p1, q1 = l.fixes()
    l.intros()
    l.simp()
    l.auto(
        by=[
            oplus_apply(A, one, p1, q1),
            nat_le.defn,
            zf.pair_inj,
            zero_ne_one,
            pfst_pair,
            le.defn,
        ]
    )
    l.unfold(bij_on)
    l.split()
    l.unfold(maps_to)
    l.fix()
    l.intro()
    l.simp()
    l.auto(by=[elem_succ])
    l.unfold(inj_on)
    p3, q3 = l.fixes()
    l.intros()
    l.simp(at=-1)
    l.auto()
    l.unfold(surj_on)
    z0 = l.fix()
    l.intro()
    l.cases(z0 == A, z0 != A)
    l.exists(top)
    l.simp()
    l.auto(by=[elem_osum_set(A, one, top), pfst_pair, elem_one])
    l.exists(pair(z0, zero))
    l.simp()
    l.auto(by=[elem_osum_set(A, one, pair(z0, zero)), pfst_pair, elem_succ])
    l.unfold(oadd)
    l.auto(
        by=[
            ord_of_eq(oplus, X, succ(A)),
            similar.defn(oplus, X, nat_le_rel, succ(A)),
            is_ordinal_succ(A),
        ]
    )


@Theorem(
    ForAll(
        [x, y],
        elem(x, omega),
        elem(y, omega),
        nat_le(x, y) == nat_le(succ(x), succ(y)),
    )
)
def nat_le_succ_succ(l):
    """Successor preserves and reflects ≤ on ω."""
    m0, n0 = l.fixes()
    l.intros()
    # m⁺ ∈ n⁺ means m⁺ ∈ n or m⁺ = n, and either way m ∈ n, as n is transitive.
    l.auto(
        by=[
            nat_le.defn(m0, n0),
            nat_le.defn(succ(m0), succ(n0)),
            succ_elem_succ(m0, n0),
            succ_inj(m0, n0),
            elem_succ(succ(m0), n0),
            elem_succ_self(m0),
            nat_is_transitive(n0),
            is_transitive.defn(n0),
            le.defn(succ(m0), n0),
        ]
    )


@Theorem(oadd(one, omega) == omega)
def one_oadd_omega(l):
    """Halmos: 1 + ω = ω, by (0, 0) ↦ 0 and (n, 1) ↦ n⁺."""
    X = osum_set(one, omega)
    bot = pair(zero, zero)
    f = Lambda(p, If(p == bot, zero, succ(pfst(p))))
    # Elements of 1 ⊕ ω are (0, 0) and (n, 1) with n ∈ ω.
    l.have(
        ForAll(
            p,
            elem(p, X),
            Or(p == bot, And(elem(pfst(p), omega), p == pair(pfst(p), one))),
        ),
        by=[elem_osum_set, elem_one],
    )
    l.have(ForAll(x, bot != pair(x, one)), by=[zf.pair_inj, zero_ne_one])
    l.have(
        ForAll(x, elem(x, omega), elem(zero, succ(x))),
        by=[comparable_zero, comparable.defn, elem_succ, zero.defn, zf.elem_emp],
    )
    l.have(is_similarity(f, oplus, X, nat_le_rel, omega))
    l.unfold(is_similarity)
    l.unfold(is_order_embedding)
    l.split()
    l.split()
    l.unfold(maps_to)
    l.fix()
    l.intro()
    l.simp()
    l.auto(by=[omega_zero, omega_succ])
    # 0 is below every n⁺, no n⁺ is ≤ 0, and n⁺ ≤ m⁺ iff n ≤ m.
    p1, q1 = l.fixes()
    l.intros()
    l.simp()
    l.auto(
        by=[
            oplus_apply(one, omega, p1, q1),
            nat_le.defn,
            zf.pair_inj,
            zero_ne_one,
            pfst_pair,
            succ_ne_zero,
            nat_le_succ_succ(pfst(p1), pfst(q1)),
            zero.defn,
            zf.elem_emp,
        ]
    )
    l.unfold(bij_on)
    l.split()
    l.unfold(maps_to)
    l.fix()
    l.intro()
    l.simp()
    l.auto(by=[omega_zero, omega_succ])
    l.unfold(inj_on)
    p3, q3 = l.fixes()
    l.intros()
    l.simp(at=-1)
    l.auto(by=[succ_ne_zero, succ_inj(pfst(p3), pfst(q3))])
    l.unfold(surj_on)
    k0 = l.fix()
    l.intro()
    l.cases(k0 == zero, k0 != zero)
    l.exists(bot)
    l.simp()
    l.auto(by=[elem_osum_set(one, omega, bot), pfst_pair, elem_one])
    l.have(
        Exists(x, And(elem(x, omega), k0 == succ(x))),
        by=[exists_eq_succ_of_ne_zero(k0)],
    )
    m0, _ = l.obtain(-1)
    l.exists(pair(m0, one))
    l.simp()
    l.auto(by=[elem_osum_set(one, omega, pair(m0, one)), pfst_pair])
    l.unfold(oadd)
    l.auto(
        by=[
            ord_of_eq(oplus, X, omega),
            similar.defn(oplus, X, nat_le_rel, omega),
            omega_is_ordinal,
        ]
    )


# Addition of ordinals is not commutative.
oadd_not_comm = prove(
    oadd(one, omega) != oadd(omega, one),
    by=[
        one_oadd_omega,
        oadd_one(omega),
        omega_is_ordinal,
        elem_succ_self(omega),
        ordinal_not_elem_self(omega, omega),
    ],
)


@Theorem(ForAll(A, is_ordinal(A), oadd(zero, A) == A))
def zero_oadd(l):
    """Halmos: 0 + α = α, by the similarity (x, 1) ↦ x."""
    A = l.fix()
    l.intro()
    X = osum_set(zero, A)
    f = Lambda(p, pfst(p))
    # Every element of 0 ⊕ α is (x, 1) with x ∈ α.
    l.have(
        ForAll(p, elem(p, X), And(elem(pfst(p), A), p == inr(pfst(p)))),
        by=[elem_osum_set, zero.defn, zf.elem_emp],
    )
    l.have(is_similarity(f, oplus, X, nat_le_rel, A))
    l.unfold(is_similarity)
    l.unfold(is_order_embedding)
    l.split()
    l.split()
    l.auto(by=[maps_to.defn(f, X, A)])
    p0, q0 = l.fixes()
    l.intros()
    l.simp()
    l.auto(by=[oplus_apply(zero, A, p0, q0), zero_ne_one, zf.pair_inj, nat_le.defn])
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
    l.exists(inr(x0))
    l.simp()
    l.auto(by=[elem_osum_set(zero, A, inr(x0)), pfst_pair])
    l.unfold(oadd)
    l.auto(by=[ord_of_eq(oplus, X, A), similar.defn(oplus, X, nat_le_rel, A)])


@Theorem(
    ForAll(
        [R, A, R2, A2, S, B, S2, B2],
        similar(R, A, R2, A2),
        similar(S, B, S2, B2),
        similar(osum_rel(R, S), osum_set(A, B), osum_rel(R2, S2), osum_set(A2, B2)),
    )
)
def similar_osum(l):
    R, A, R2, A2, S, B, S2, B2 = l.fixes()
    l.intros()
    l.unfold(similar, at=0)
    l.unfold(similar, at=1)
    f0, _ = l.obtain(0)
    g0, _ = l.obtain(1)
    l.unfold(similar)
    l.exists(osum_map(f0, g0))
    l.auto(by=[similarity_osum(f0, g0, R, A, R2, A2, S, B, S2, B2)])


# Regrouping (A ⊕ B) ⊕ C as A ⊕ (B ⊕ C).
osum_assoc_map = define_const(
    "osum_assoc_map",
    Lambda(
        p,
        If(
            p == inr(pfst(p)),
            inr(inr(pfst(p))),
            If(
                pfst(p) == inl(pfst(pfst(p))),
                inl(pfst(pfst(p))),
                inr(inl(pfst(pfst(p)))),
            ),
        ),
    ),
)


@Theorem(
    ForAll(
        x,
        And(
            Select(osum_assoc_map, inl(inl(x))) == inl(x),
            Select(osum_assoc_map, inl(inr(x))) == inr(inl(x)),
            Select(osum_assoc_map, inr(x)) == inr(inr(x)),
        ),
    )
)
def osum_assoc_map_apply(l):
    l.fix()
    l.unfold(osum_assoc_map)
    l.simp()
    l.auto(by=[pfst_pair, zf.pair_inj, zero_ne_one])


T = Consts("T", ArraySort(ZFSet, ZFSet, BoolSort()))[0]
C = Consts("C", ZFSet)[0]


@Theorem(
    ForAll(
        [R, S, T, A, B, C],
        is_similarity(
            osum_assoc_map,
            osum_rel(osum_rel(R, S), T),
            osum_set(osum_set(A, B), C),
            osum_rel(R, osum_rel(S, T)),
            osum_set(A, osum_set(B, C)),
        ),
    )
)
def similarity_osum_assoc(l):
    """Halmos: the ordinal sum is associative up to similarity."""
    R, S, T, A, B, C = l.fixes()
    X, Y = osum_set(osum_set(A, B), C), osum_set(A, osum_set(B, C))
    # Elements of (A ⊕ B) ⊕ C are ((a, 0), 0), ((b, 1), 0) and (c, 1).
    l.have(
        ForAll(
            p,
            elem(p, X),
            Or(
                And(elem(pfst(pfst(p)), A), p == inl(inl(pfst(pfst(p))))),
                And(elem(pfst(pfst(p)), B), p == inl(inr(pfst(pfst(p))))),
                And(elem(pfst(p), C), p == inr(pfst(p))),
            ),
        ),
        by=[elem_osum_set],
    )
    tags = [zf.pair_inj, zero_ne_one, pfst_pair]
    l.have(
        ForAll(x, elem(x, A), elem(inl(x), Y)),
        by=[elem_osum_set] + tags,
    )
    l.have(
        ForAll(x, elem(x, B), elem(inr(inl(x)), Y)),
        by=[elem_osum_set] + tags,
    )
    l.have(
        ForAll(x, elem(x, C), elem(inr(inr(x)), Y)),
        by=[elem_osum_set] + tags,
    )
    l.unfold(is_similarity)
    l.unfold(is_order_embedding)
    l.split()
    l.split()
    l.unfold(maps_to)
    p0 = l.fix()
    l.intro()
    l.auto(by=[osum_assoc_map_apply(pfst(p0)), osum_assoc_map_apply(pfst(pfst(p0)))])
    # Compare elements part by part.
    p1, q1 = l.fixes()
    l.intros()
    l.auto(
        by=[
            osum_assoc_map_apply(pfst(p1)),
            osum_assoc_map_apply(pfst(pfst(p1))),
            osum_assoc_map_apply(pfst(q1)),
            osum_assoc_map_apply(pfst(pfst(q1))),
        ]
        + osum_rel_pairs
    )
    l.unfold(bij_on)
    l.split()
    l.unfold(maps_to)
    p2 = l.fix()
    l.intro()
    l.auto(by=[osum_assoc_map_apply(pfst(p2)), osum_assoc_map_apply(pfst(pfst(p2)))])
    l.unfold(inj_on)
    p3, q3 = l.fixes()
    l.intros()
    l.auto(
        by=[
            osum_assoc_map_apply(pfst(p3)),
            osum_assoc_map_apply(pfst(pfst(p3))),
            osum_assoc_map_apply(pfst(q3)),
            osum_assoc_map_apply(pfst(pfst(q3))),
        ]
        + tags
    )
    # Each element of A ⊕ (B ⊕ C) is hit.
    l.unfold(surj_on)
    y0 = l.fix()
    l.intro()
    l.have(
        Or(
            And(elem(pfst(y0), A), y0 == inl(pfst(y0))),
            And(elem(pfst(pfst(y0)), B), y0 == inr(inl(pfst(pfst(y0))))),
            And(elem(pfst(pfst(y0)), C), y0 == inr(inr(pfst(pfst(y0))))),
        ),
        by=[elem_osum_set(A, osum_set(B, C), y0), elem_osum_set(B, C, pfst(y0))],
    )
    y1, y2 = pfst(y0), pfst(pfst(y0))
    l.cases(
        And(elem(y1, A), y0 == inl(y1)),
        And(elem(y2, B), y0 == inr(inl(y2))),
        And(elem(y2, C), y0 == inr(inr(y2))),
    )
    l.exists(inl(inl(y1)))
    l.auto(by=[osum_assoc_map_apply(y1), elem_osum_set] + tags)
    l.exists(inl(inr(y2)))
    l.auto(by=[osum_assoc_map_apply(y2), elem_osum_set] + tags)
    l.exists(inr(y2))
    l.auto(by=[osum_assoc_map_apply(y2), elem_osum_set] + tags)


@Theorem(
    ForAll(
        [A, B],
        is_ordinal(A),
        is_ordinal(B),
        And(
            is_ordinal(oadd(A, B)),
            similar(nat_le_rel, oadd(A, B), oplus, osum_set(A, B)),
        ),
    )
)
def oadd_spec(l):
    """α + β is an ordinal similar to α ⊕ β (the counting theorem)."""
    A, B = l.fixes()
    l.intros()
    X = osum_set(A, B)
    l.have(
        is_well_order(oplus, X),
        by=[
            osum_well_order(nat_le_rel, nat_le_rel, A, B),
            ordinal_well_order(A),
            ordinal_well_order(B),
        ],
    )
    l.unfold(oadd)
    l.auto(
        by=[
            counting_theorem(oplus, X),
            similar_symm(oplus, X, nat_le_rel, ord_of(oplus, X)),
        ]
    )


@Theorem(
    ForAll(
        [A, B, C],
        is_ordinal(A),
        is_ordinal(B),
        is_ordinal(C),
        oadd(oadd(A, B), C) == oadd(A, oadd(B, C)),
    )
)
def oadd_assoc(l):
    """Halmos: (α + β) + γ = α + (β + γ)."""
    A, B, C = l.fixes()
    l.intros()
    AB, BC = oadd(A, B), oadd(B, C)
    l.have(
        And(is_ordinal(AB), similar(nat_le_rel, AB, oplus, osum_set(A, B))),
        by=[oadd_spec(A, B)],
    )
    l.have(
        And(is_ordinal(BC), similar(nat_le_rel, BC, oplus, osum_set(B, C))),
        by=[oadd_spec(B, C)],
    )
    l.have(is_ordinal(oadd(A, BC)), by=[oadd_spec(A, BC)])
    # (α + β) ⊕ γ ≅ (α ⊕ β) ⊕ γ ≅ α ⊕ (β ⊕ γ) ≅ α ⊕ (β + γ) ≅ α + (β + γ).
    X1 = osum_set(AB, C)
    X2 = osum_set(osum_set(A, B), C)
    X3 = osum_set(A, osum_set(B, C))
    X4 = osum_set(A, BC)
    R2 = osum_rel(oplus, nat_le_rel)
    R3 = osum_rel(nat_le_rel, oplus)
    l.have(
        similar(oplus, X1, R2, X2),
        by=[
            similar_osum(
                nat_le_rel, AB, oplus, osum_set(A, B), nat_le_rel, C, nat_le_rel, C
            ),
            similar_refl(nat_le_rel, C),
        ],
    )
    l.have(
        similar(R2, X2, R3, X3),
        by=[
            similar.defn(R2, X2, R3, X3),
            similarity_osum_assoc(nat_le_rel, nat_le_rel, nat_le_rel, A, B, C),
        ],
    )
    l.have(
        similar(R3, X3, oplus, X4),
        by=[
            similar_osum(
                nat_le_rel, A, nat_le_rel, A, oplus, osum_set(B, C), nat_le_rel, BC
            ),
            similar_refl(nat_le_rel, A),
            similar_symm(nat_le_rel, BC, oplus, osum_set(B, C)),
        ],
    )
    l.have(
        similar(oplus, X4, nat_le_rel, oadd(A, BC)),
        by=[
            oadd_spec(A, BC),
            similar_symm(nat_le_rel, oadd(A, BC), oplus, X4),
        ],
    )
    l.have(similar(oplus, X1, R3, X3), by=[similar_trans(oplus, X1, R2, X2, R3, X3)])
    l.have(
        similar(oplus, X1, oplus, X4), by=[similar_trans(oplus, X1, R3, X3, oplus, X4)]
    )
    l.have(
        similar(oplus, X1, nat_le_rel, oadd(A, BC)),
        by=[similar_trans(oplus, X1, oplus, X4, nat_le_rel, oadd(A, BC))],
    )
    l.auto(by=[oadd.defn(AB, C), ord_of_eq(oplus, X1, oadd(A, BC))])
