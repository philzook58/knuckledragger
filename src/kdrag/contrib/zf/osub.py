"""
Ordinal subtraction (Halmos §21).

If α ≤ β, there is a unique γ with α + γ = β. Halmos takes γ to be the ordinal
of the remainder β − α: α ⊕ (β − α) is similar to β by (x, 0) ↦ x, (x, 1) ↦ x.
Uniqueness is left cancellation, which follows from strict monotonicity of
α + γ in γ: α ⊕ γ is an initial segment of α ⊕ δ when γ < δ.
"""

from kdrag import Theorem, define
from kdrag.smt import And, Consts, ForAll, Lambda, Not, Or
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import ZFSet, elem, le
from kdrag.contrib.zf.count import counting_theorem, ord_of, ord_of_eq
from kdrag.contrib.zf.fun import bij_on, elem_sub, inj_on, maps_to, pfst, pfst_pair, surj_on
from kdrag.contrib.zf.oarith import (
    oadd,
    oadd_spec,
    oplus,
    oplus_apply,
    osum_rel_inl_inr,
    osum_rel_inr_inr,
    similar_osum,
)
from kdrag.contrib.zf.order import nat_le
from kdrag.contrib.zf.ordinal import is_ordinal, is_ordinal_of_elem, well_order_subset
from kdrag.contrib.zf.ordset import (
    ordinal_comparable,
    ordinal_le_of_elem,
    ordinal_not_elem_self,
    ordinal_well_order,
)
from kdrag.contrib.zf.poset import elem_seg_iff, is_well_order, nat_le_rel, seg
from kdrag.contrib.zf.sim import (
    is_order_embedding,
    is_similarity,
    similar,
    similar_refl,
    similar_symm,
    similar_trans,
    similarity_seg,
)
from kdrag.contrib.zf.dsum import elem_osum_set, inl, inr, osum_set
from kdrag.contrib.zf.nat import zero_ne_one

A, B, C, D, a, d, p, q, x, y = Consts("A B C D a d p q x y", ZFSet)

# β − α is the ordinal of the remainder β \ α.
osub = define("osub", [B, A], ord_of(nat_le_rel, B - A))


@Theorem(
    ForAll(
        [A, B, a, d],
        is_ordinal(A),
        is_ordinal(B),
        elem(a, A),
        elem(d, B),
        Not(elem(d, A)),
        elem(a, d),
    )
)
def elem_of_not_elem(l):
    """An element of β outside α lies above every element of α."""
    A, B, a, d = l.fixes()
    l.intros()
    l.have(is_ordinal(d), by=[is_ordinal_of_elem(B, d)])
    # d ∈ α is excluded; d = α contains a; α ∈ d gives a ∈ d by transitivity.
    l.auto(by=[ordinal_comparable(A, d), ordinal_le_of_elem(d, A), le.defn(A, d)])


@Theorem(
    ForAll(
        [A, B],
        is_ordinal(A),
        is_ordinal(B),
        A <= B,
        And(
            is_ordinal(osub(B, A)),
            similar(oplus, osum_set(A, B - A), nat_le_rel, B),
            similar(nat_le_rel, B - A, nat_le_rel, osub(B, A)),
        ),
    )
)
def osub_spec(l):
    """Halmos: α ⊕ (β − α) is similar to β, by (x, 0) ↦ x and (x, 1) ↦ x."""
    A, B = l.fixes()
    l.intros()
    Dif = B - A
    X = osum_set(A, Dif)
    l.have(ForAll(x, elem(x, Dif) == And(elem(x, B), Not(elem(x, A)))), by=[elem_sub])
    l.have(
        is_well_order(nat_le_rel, Dif),
        by=[well_order_subset(nat_le_rel, B, Dif), ordinal_well_order(B), le.defn],
    )
    l.have(
        And(is_ordinal(osub(B, A)), similar(nat_le_rel, Dif, nat_le_rel, osub(B, A))),
        by=[counting_theorem(nat_le_rel, Dif), osub.defn(B, A)],
    )
    f = Lambda(p, pfst(p))
    # Elements of α ⊕ (β − α) are (x, 0) with x ∈ α and (x, 1) with x ∈ β − α.
    l.have(
        ForAll(
            p,
            elem(p, X),
            Or(
                And(elem(pfst(p), A), p == inl(pfst(p))), And(elem(pfst(p), Dif), p == inr(pfst(p)))
            ),
        ),
        by=[elem_osum_set],
    )
    l.have(is_similarity(f, oplus, X, nat_le_rel, B))
    l.unfold(is_similarity)
    l.unfold(is_order_embedding)
    l.unfold(bij_on)
    l.split()
    l.split()
    l.auto(by=[maps_to.defn(f, X, B), le.defn(A, B)])
    # Within each part the order is ≤, and α comes before β − α.
    p1, q1 = l.fixes()
    l.intros()
    l.simp()
    x1, y1 = pfst(p1), pfst(q1)
    l.auto(
        by=[
            oplus_apply(A, Dif, p1, q1),
            nat_le.defn,
            zf.pair_inj,
            zero_ne_one,
            elem_of_not_elem(A, B, x1, y1),
            elem_of_not_elem(A, B, y1, x1),
            ordinal_le_of_elem(A, y1),
            le.defn(y1, A),
        ]
    )
    l.split()
    l.auto(by=[maps_to.defn(f, X, B), le.defn(A, B)])
    l.unfold(inj_on)
    p2, q2 = l.fixes()
    l.intros()
    l.simp(at=-1)
    l.auto()
    l.unfold(surj_on)
    b0 = l.fix()
    l.intro()
    l.cases(elem(b0, A), Not(elem(b0, A)))
    l.exists(inl(b0))
    l.simp()
    l.auto(by=[elem_osum_set(A, Dif, inl(b0)), pfst_pair])
    l.exists(inr(b0))
    l.simp()
    l.auto(by=[elem_osum_set(A, Dif, inr(b0)), pfst_pair])
    l.auto(by=[similar.defn(oplus, X, nat_le_rel, B)])


@Theorem(ForAll([A, B], is_ordinal(A), is_ordinal(B), A <= B, oadd(A, osub(B, A)) == B))
def oadd_osub_cancel_of_le(l):
    """Halmos: if α ≤ β then α + (β − α) = β."""
    A, B = l.fixes()
    l.intros()
    G = osub(B, A)
    X = osum_set(A, G)
    Y = osum_set(A, B - A)
    l.have(
        And(
            is_ordinal(G),
            similar(oplus, Y, nat_le_rel, B),
            similar(nat_le_rel, B - A, nat_le_rel, G),
        ),
        by=[osub_spec(A, B)],
    )
    # α ⊕ γ ≅ α ⊕ (β − α) ≅ β
    l.have(
        similar(oplus, X, oplus, Y),
        by=[
            similar_osum(nat_le_rel, A, nat_le_rel, A, nat_le_rel, G, nat_le_rel, B - A),
            similar_refl(nat_le_rel, A),
            similar_symm(nat_le_rel, B - A, nat_le_rel, G),
        ],
    )
    l.have(similar(oplus, X, nat_le_rel, B), by=[similar_trans(oplus, X, oplus, Y, nat_le_rel, B)])
    l.auto(by=[oadd.defn(A, G), ord_of_eq(oplus, X, B)])


@Theorem(
    ForAll(
        [A, C, D], is_ordinal(D), elem(C, D), seg(oplus, osum_set(A, D), inr(C)) == osum_set(A, C)
    )
)
def seg_osum_inr(l):
    """In α ⊕ δ the elements before (γ, 1) form α ⊕ γ."""
    A, C, D = l.fixes()
    l.intros()
    l.have(C <= D, by=[ordinal_le_of_elem(D, C)])
    l.rw(zf.ext_ax)
    p0 = l.fix()
    x0 = pfst(p0)
    l.rw(elem_seg_iff)
    tags = [elem_osum_set(A, D, p0), elem_osum_set(A, C, p0), zf.pair_inj, zero_ne_one]
    l.cases(p0 == inl(x0), p0 == inr(x0), And(p0 != inl(x0), p0 != inr(x0)))
    # (x, 0) is in both sides exactly when x ∈ α.
    l.auto(by=[osum_rel_inl_inr(nat_le_rel, nat_le_rel, x0, C)] + tags)
    # (x, 1) precedes (γ, 1) iff x < γ, and then x ∈ δ.
    l.have(
        oplus[p0, inr(C)] == Or(elem(x0, C), x0 == C),
        by=[osum_rel_inr_inr(nat_le_rel, nat_le_rel, x0, C), nat_le.defn(x0, C)],
    )
    l.have((p0 == inr(C)) == (x0 == C), by=[zf.pair_inj])
    l.have(p0 != inl(x0), by=[zf.pair_inj, zero_ne_one])
    # γ ∉ γ, and x ∈ γ ⊆ δ.
    l.have(elem(x0, C) == And(elem(x0, D), elem(x0, C)), by=[le.defn(C, D)])
    l.auto(by=[elem_osum_set(A, D, p0), elem_osum_set(A, C, p0), ordinal_not_elem_self(D, C)])
    # Anything else is in neither side.
    l.auto(by=tags)


@Theorem(ForAll([A, C, D], is_ordinal(A), is_ordinal(D), elem(C, D), elem(oadd(A, C), oadd(A, D))))
def oadd_elem_oadd(l):
    """Halmos: γ < δ implies α + γ < α + δ. A similarity h of α ⊕ δ onto α + δ
    carries the initial segment α ⊕ γ onto the initial segment before h(γ, 1),
    which in an ordinal is h(γ, 1) itself."""
    A, C, D = l.fixes()
    l.intros()
    AD = oadd(A, D)
    Y = osum_set(A, D)
    l.have(And(is_ordinal(AD), similar(nat_le_rel, AD, oplus, Y)), by=[oadd_spec(A, D)])
    l.have(similar(oplus, Y, nat_le_rel, AD), by=[similar_symm(nat_le_rel, AD, oplus, Y)])
    l.unfold(similar, at=-1)
    h, _ = l.obtain(-1)
    t = inr(C)
    l.have(elem(t, Y), by=[elem_osum_set(A, D, t), pfst_pair])
    n0 = h[t]
    l.have(
        elem(n0, AD),
        by=[
            is_similarity.defn(h, oplus, Y, nat_le_rel, AD),
            is_order_embedding.defn(h, oplus, Y, nat_le_rel, AD),
            maps_to.defn(h, Y, AD),
        ],
    )
    l.have(seg(nat_le_rel, AD, n0) == n0, by=[is_ordinal.defn(AD)])
    l.have(
        is_similarity(h, oplus, osum_set(A, C), nat_le_rel, n0),
        by=[similarity_seg(h, oplus, Y, nat_le_rel, AD, t), seg_osum_inr(A, C, D)],
    )
    l.have(is_ordinal(n0), by=[is_ordinal_of_elem(AD, n0)])
    l.auto(
        by=[
            oadd.defn(A, C),
            ord_of_eq(oplus, osum_set(A, C), n0),
            similar.defn(oplus, osum_set(A, C), nat_le_rel, n0),
        ]
    )


@Theorem(
    ForAll([A, C, D], is_ordinal(A), is_ordinal(C), is_ordinal(D), oadd(A, C) == oadd(A, D), C == D)
)
def oadd_left_cancel(l):
    """Halmos: α + γ = α + δ implies γ = δ, so β − α is the unique solution."""
    A, C, D = l.fixes()
    l.intros()
    l.have(is_ordinal(oadd(A, D)), by=[oadd_spec(A, D)])
    l.auto(
        by=[
            ordinal_comparable(C, D),
            oadd_elem_oadd(A, C, D),
            oadd_elem_oadd(A, D, C),
            ordinal_not_elem_self(oadd(A, D), oadd(A, D)),
        ]
    )


@Theorem(
    ForAll(
        [A, B, C],
        is_ordinal(A),
        is_ordinal(B),
        is_ordinal(C),
        A <= B,
        (oadd(A, C) == B) == (C == osub(B, A)),
    )
)
def oadd_eq_iff_eq_osub(l):
    """Halmos §21: for α ≤ β, β − α is the one ordinal γ with α + γ = β."""
    A, B, C = l.fixes()
    l.intros()
    l.have(is_ordinal(osub(B, A)), by=[osub_spec(A, B)])
    l.auto(by=[oadd_osub_cancel_of_le(A, B), oadd_left_cancel(A, C, osub(B, A))])
