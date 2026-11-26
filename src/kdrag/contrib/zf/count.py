"""
The counting theorem (Halmos §20): each well ordered set is similar to a
unique ordinal number.

`ord_of(R, X)` is that ordinal, named with definite description. The proof
follows Halmos: if every initial segment s(x) of X is similar to an ordinal,
the axiom of substitution collects those ordinals into a set, which is an
ordinal similar to X; transfinite induction then covers every s(a), and X.
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
    Or,
)
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import ZFSet, elem, le
from kdrag.contrib.zf.finite import inv as inverse
from kdrag.contrib.zf.fun import bij_on, inj_on, maps_to, surj_on
from kdrag.contrib.zf.nat import is_transitive
from kdrag.contrib.zf.ordinal import (
    elem_repl,
    is_ordinal,
    is_ordinal_of_elem,
    repl,
    the,
    the_eq,
    well_order_subset,
)
from kdrag.contrib.zf.order import nat_le
from kdrag.contrib.zf.ordset import (
    eq_of_similarity,
    is_ordinal_of_transitive,
    ordinal_le_of_elem,
    ordinal_not_elem_self,
)
from kdrag.contrib.zf.poset import (
    elem_seg_iff,
    is_partial_order,
    is_total_order,
    is_well_order,
    nat_le_rel,
    partial_order_antisymm,
    partial_order_of_well_order,
    partial_order_refl,
    seg,
    seg_seg,
    total_order_of_well_order,
    well_order_induction,
)
from kdrag.contrib.zf.sim import (
    is_order_embedding,
    is_similarity,
    similar,
    similarity_comp,
    similarity_inv,
    similarity_seg,
)

A, B, X, a, b, x, y = Consts("A B X a b x y", ZFSet)
R = Consts("R", ArraySort(ZFSet, ZFSet, BoolSort()))[0]
f, g, h = Consts("f g h", ArraySort(ZFSet, ZFSet))

# The ordinal similar to X, when there is one.
ord_of = define(
    "ord_of", [R, X], the(Lambda(a, And(is_ordinal(a), similar(R, X, nat_le_rel, a))))
)


@Theorem(
    ForAll(
        [R, X, A, B],
        is_ordinal(A),
        is_ordinal(B),
        similar(R, X, nat_le_rel, A),
        similar(R, X, nat_le_rel, B),
        A == B,
    )
)
def ordinal_similar_unique(l):
    """Halmos: since for ordinals similarity is equality, a set is similar to at most
    one ordinal."""
    R, X, A, B = l.fixes()
    l.intros()
    l.unfold(similar, at=2)
    l.unfold(similar, at=3)
    g0, _ = l.obtain(2)
    h0, _ = l.obtain(3)
    # h g⁻¹ is a similarity from α onto β.
    hg = Lambda(x, h0[inverse(g0, X)[x]])
    l.have(
        is_similarity(hg, nat_le_rel, A, nat_le_rel, B),
        by=[
            similarity_inv(g0, R, X, nat_le_rel, A),
            similarity_comp(inverse(g0, X), h0, nat_le_rel, A, R, X, nat_le_rel, B),
        ],
    )
    l.auto(by=[eq_of_similarity(hg, A, B)])


@Theorem(
    ForAll([R, X, A], is_ordinal(A), similar(R, X, nat_le_rel, A), ord_of(R, X) == A)
)
def ord_of_eq(l):
    """If X is similar to the ordinal α, then ord_of(R, X) is α."""
    R, X, A = l.fixes()
    l.intros()
    l.unfold(ord_of)
    P = Lambda(a, And(is_ordinal(a), similar(R, X, nat_le_rel, a)))
    l.have(ForAll(b, P[b], b == A))
    b0 = l.fix()
    l.intro()
    l.simp(at=-1)
    l.auto(by=[ordinal_similar_unique(R, X, b0, A)])
    l.have(P[A])
    l.simp()
    l.auto()
    l.auto(by=[the_eq(P, A)])


seg_ordinal = prove(
    ForAll([A, x], is_ordinal(A), elem(x, A), seg(nat_le_rel, A, x) == x),
    by=[is_ordinal.defn],
)


# ord_seg(x) is the ordinal similar to the initial segment s(x).
ord_seg = define("ord_seg", [R, X, x], ord_of(R, seg(R, X, x)))
# Every initial segment of X is similar to some ordinal.
segs_similar_ordinal = define(
    "segs_similar_ordinal",
    [R, X],
    ForAll(
        x,
        elem(x, X),
        Exists(a, And(is_ordinal(a), similar(R, seg(R, X, x), nat_le_rel, a))),
    ),
)


@Theorem(
    ForAll(
        [R, X, x],
        segs_similar_ordinal(R, X),
        elem(x, X),
        And(
            is_ordinal(ord_seg(R, X, x)),
            similar(R, seg(R, X, x), nat_le_rel, ord_seg(R, X, x)),
        ),
    )
)
def ord_seg_spec(l):
    R, X, x0 = l.fixes()
    l.intros()
    l.have(
        Exists(a, And(is_ordinal(a), similar(R, seg(R, X, x0), nat_le_rel, a))),
        by=[segs_similar_ordinal.defn(R, X)],
    )
    a0, _ = l.obtain(-1)
    l.auto(by=[ord_seg.defn(R, X, x0), ord_of_eq(R, seg(R, X, x0), a0)])


@Theorem(
    ForAll(
        [g, R, X, x, y],
        is_well_order(R, X),
        segs_similar_ordinal(R, X),
        elem(y, X),
        is_similarity(g, R, seg(R, X, y), nat_le_rel, ord_seg(R, X, y)),
        elem(x, seg(R, X, y)),
        ord_seg(R, X, x) == g[x],
    )
)
def ord_seg_eq_apply(l):
    """Halmos: a similarity g of s(y) onto its ordinal maps s(x) onto s(g(x)) = g(x),
    so the ordinal of s(x) is g(x)."""
    g0, R, X, x0, y0 = l.fixes()
    l.intros()
    sy, Fy = seg(R, X, y0), ord_seg(R, X, y0)
    l.have(is_ordinal(Fy), by=[ord_seg_spec(R, X, y0)])
    gx = g0[x0]
    l.have(
        elem(gx, Fy),
        by=[is_similarity.defn, is_order_embedding.defn, maps_to.defn(g0, sy, Fy)],
    )
    l.have(is_ordinal(gx), by=[is_ordinal_of_elem(Fy, gx)])
    l.have(
        is_similarity(g0, R, seg(R, sy, x0), nat_le_rel, seg(nat_le_rel, Fy, gx)),
        by=[similarity_seg(g0, R, sy, nat_le_rel, Fy, x0), elem_seg_iff(R, X, y0, x0)],
    )
    l.have(
        seg(R, sy, x0) == seg(R, X, x0),
        by=[seg_seg(R, X, y0, x0), partial_order_of_well_order(R, X)],
    )
    l.have(seg(nat_le_rel, Fy, gx) == gx, by=[seg_ordinal(Fy, gx)])
    l.have(
        similar(R, seg(R, X, x0), nat_le_rel, gx),
        by=[similar.defn(R, seg(R, X, x0), nat_le_rel, gx)],
    )
    l.auto(by=[ord_seg.defn(R, X, x0), ord_of_eq(R, seg(R, X, x0), gx)])


@Theorem(
    ForAll(
        [R, X, x, y],
        is_well_order(R, X),
        segs_similar_ordinal(R, X),
        elem(x, X),
        elem(y, X),
        R[x, y],
        x != y,
        elem(ord_seg(R, X, x), ord_seg(R, X, y)),
    )
)
def ord_seg_elem(l):
    """For x < y, the ordinal of s(x) is an element of the ordinal of s(y)."""
    R, X, x0, y0 = l.fixes()
    l.intros()
    sy, Fy = seg(R, X, y0), ord_seg(R, X, y0)
    l.have(similar(R, sy, nat_le_rel, Fy), by=[ord_seg_spec(R, X, y0)])
    l.have(
        Exists(g, is_similarity(g, R, sy, nat_le_rel, Fy)),
        by=[similar.defn(R, sy, nat_le_rel, Fy)],
    )
    g0, _ = l.obtain(-1)
    l.have(elem(x0, sy), by=[elem_seg_iff(R, X, y0, x0)])
    l.have(ord_seg(R, X, x0) == g0[x0], by=[ord_seg_eq_apply(g0, R, X, x0, y0)])
    l.auto(by=[is_similarity.defn, is_order_embedding.defn, maps_to.defn(g0, sy, Fy)])


# Halmos: the axiom of substitution collects the ordinals of the initial segments.
ord_segs = define("ord_segs", [R, X], repl(Lambda(x, ord_seg(R, X, x)), X))


@Theorem(
    ForAll(
        [R, X, y],
        elem(y, ord_segs(R, X)) == Exists(x, And(elem(x, X), ord_seg(R, X, x) == y)),
    )
)
def elem_ord_segs(l):
    R, X, y0 = l.fixes()
    l.unfold(ord_segs)
    l.rw(elem_repl)
    l.simp()
    l.auto()


@Theorem(
    ForAll(
        [R, X],
        is_well_order(R, X),
        segs_similar_ordinal(R, X),
        is_ordinal(ord_segs(R, X)),
    )
)
def is_ordinal_ord_segs(l):
    """The collected ordinals form a transitive set of ordinals, hence an ordinal."""
    R, X = l.fixes()
    l.intros()
    B = ord_segs(R, X)
    l.have(ForAll(a, elem(a, B), is_ordinal(a)))
    a0 = l.fix()
    l.intro()
    l.have(
        Exists(x, And(elem(x, X), ord_seg(R, X, x) == a0)), by=[elem_ord_segs(R, X, a0)]
    )
    x0, _ = l.obtain(-1)
    l.auto(by=[ord_seg_spec(R, X, x0)])
    # ζ ∈ ord(s(y)) is g(η) for a similarity g of s(y), and g(η) = ord(s(η)) ∈ B.
    l.have(is_transitive(B))
    l.unfold(is_transitive)
    b0 = l.fix()
    l.intro()
    l.unfold(le)
    z0 = l.fix()
    l.intro()
    l.have(
        Exists(y, And(elem(y, X), ord_seg(R, X, y) == b0)), by=[elem_ord_segs(R, X, b0)]
    )
    y0, _ = l.obtain(-1)
    sy, Fy = seg(R, X, y0), ord_seg(R, X, y0)
    l.have(similar(R, sy, nat_le_rel, Fy), by=[ord_seg_spec(R, X, y0)])
    l.have(
        Exists(g, is_similarity(g, R, sy, nat_le_rel, Fy)),
        by=[similar.defn(R, sy, nat_le_rel, Fy)],
    )
    g0, _ = l.obtain(-1)
    l.have(
        Exists(x, And(elem(x, sy), g0[x] == z0)),
        by=[
            is_similarity.defn(g0, R, sy, nat_le_rel, Fy),
            bij_on.defn(g0, sy, Fy),
            surj_on.defn(g0, sy, Fy),
        ],
    )
    e0, _ = l.obtain(-1)
    l.have(ord_seg(R, X, e0) == g0[e0], by=[ord_seg_eq_apply(g0, R, X, e0, y0)])
    l.auto(by=[elem_ord_segs(R, X, z0), elem_seg_iff(R, X, y0, e0)])
    l.auto(by=[is_ordinal_of_transitive(B)])


@Theorem(
    ForAll(
        [R, X],
        is_well_order(R, X),
        segs_similar_ordinal(R, X),
        is_similarity(Lambda(x, ord_seg(R, X, x)), R, X, nat_le_rel, ord_segs(R, X)),
    )
)
def similarity_ord_segs(l):
    """x ↦ ord(s(x)) is a similarity of X onto the collected ordinals."""
    R, X = l.fixes()
    l.intros()
    l.have(is_partial_order(R, X), by=[partial_order_of_well_order(R, X)])
    l.have(
        ForAll([x, y], elem(x, X), elem(y, X), Or(R[x, y], R[y, x])),
        by=[total_order_of_well_order(R, X), is_total_order.defn(R, X)],
    )
    # x ≤ y iff ord(s(x)) ≤ ord(s(y)): one way is ord_seg_elem, the other uses
    # totality and that ordinals are not members of themselves.
    l.have(
        ForAll(
            [x, y],
            elem(x, X),
            elem(y, X),
            R[x, y] == nat_le(ord_seg(R, X, x), ord_seg(R, X, y)),
        )
    )
    x0, y0 = l.fixes()
    l.intros()
    Fx, Fy = ord_seg(R, X, x0), ord_seg(R, X, y0)
    l.have(
        Implies(And(R[x0, y0], x0 != y0), elem(Fx, Fy)), by=[ord_seg_elem(R, X, x0, y0)]
    )
    l.have(
        Implies(And(R[y0, x0], y0 != x0), elem(Fy, Fx)), by=[ord_seg_elem(R, X, y0, x0)]
    )
    l.have(is_ordinal(Fy), by=[ord_seg_spec(R, X, y0)])
    l.have(is_ordinal(Fx), by=[ord_seg_spec(R, X, x0)])
    l.auto(
        by=[
            nat_le.defn(Fx, Fy),
            partial_order_refl(R, X, x0),
            ordinal_not_elem_self(Fy, Fx),
            ordinal_not_elem_self(Fx, Fy),
            ordinal_le_of_elem(Fx, Fy),
            le.defn(Fy, Fx),
        ]
    )
    l.unfold(is_similarity)
    l.unfold(is_order_embedding)
    l.split()
    l.split()
    l.unfold(maps_to)
    x1 = l.fix()
    l.intro()
    l.simp()
    l.auto(by=[elem_ord_segs(R, X, ord_seg(R, X, x1))])
    x2, y2 = l.fixes()
    l.intros()
    l.simp()
    l.auto(by=[nat_le.defn])
    l.unfold(bij_on)
    l.split()
    l.unfold(maps_to)
    x3 = l.fix()
    l.intro()
    l.simp()
    l.auto(by=[elem_ord_segs(R, X, ord_seg(R, X, x3))])
    # One-to-one: equal ordinals give x ≤ y and y ≤ x.
    l.unfold(inj_on)
    x4, y4 = l.fixes()
    l.intros()
    l.simp(at=-1)
    l.auto(by=[nat_le.defn, partial_order_antisymm(R, X, x4, y4)])
    l.unfold(surj_on)
    b0 = l.fix()
    l.intro()
    l.simp()
    l.auto(by=[elem_ord_segs(R, X, b0)])


exists_ordinal_similar_of_segs = prove(
    ForAll(
        [R, X],
        is_well_order(R, X),
        segs_similar_ordinal(R, X),
        Exists(a, And(is_ordinal(a), similar(R, X, nat_le_rel, a))),
    ),
    by=[is_ordinal_ord_segs, similarity_ord_segs, similar.defn],
)


@Theorem(
    ForAll(
        [R, X],
        is_well_order(R, X),
        And(is_ordinal(ord_of(R, X)), similar(R, X, nat_le_rel, ord_of(R, X))),
    )
)
def counting_theorem(l):
    """Halmos §20: each well ordered set is similar to a unique ordinal number,
    ord_of(R, X) (unique by `ordinal_similar_unique`)."""
    R, X = l.fixes()
    l.intro()
    P = Lambda(
        a, Exists(b, And(is_ordinal(b), similar(R, seg(R, X, a), nat_le_rel, b)))
    )
    # By transfinite induction every s(a) is similar to an ordinal: the segments of
    # s(a) are segments s(x) of X, so the step is the case X := s(a) of the
    # collection argument.
    l.have(ForAll(a, elem(a, X), P[a]))
    l.have(ForAll(a, elem(a, X), ForAll(b, elem(b, seg(R, X, a)), P[b]), P[a]))
    a0 = l.fix()
    l.intros()
    sa = seg(R, X, a0)
    l.have(
        is_well_order(R, sa),
        by=[well_order_subset(R, X, sa), seg.defn, zf.elem_sep, le.defn],
    )
    l.have(segs_similar_ordinal(R, sa))
    l.unfold(segs_similar_ordinal)
    x0 = l.fix()
    l.intro()
    l.have(
        seg(R, sa, x0) == seg(R, X, x0),
        by=[seg_seg(R, X, a0, x0), partial_order_of_well_order(R, X)],
    )
    l.have(P[x0])
    l.auto()
    l.simp(at=-1)
    l.auto()
    l.simp()
    l.auto(by=[exists_ordinal_similar_of_segs(R, sa)])
    l.auto(by=[well_order_induction(R, X, P)])
    # The same argument for X itself.
    l.have(segs_similar_ordinal(R, X))
    l.unfold(segs_similar_ordinal)
    x1 = l.fix()
    l.intro()
    l.have(P[x1])
    l.auto()
    l.simp(at=-1)
    l.auto()
    l.have(
        Exists(a, And(is_ordinal(a), similar(R, X, nat_le_rel, a))),
        by=[exists_ordinal_similar_of_segs(R, X)],
    )
    a1, _ = l.obtain(-1)
    l.auto(by=[ord_of_eq(R, X, a1)])
