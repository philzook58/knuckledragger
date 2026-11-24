"""
Similarity of ordered sets (Halmos §18).

A similarity is a one-to-one correspondence f from X onto Y with
a ≤ b iff f(a) ≤ f(b). The central fact is Halmos' lemma that an
order-preserving map of a well ordered set into itself satisfies a ≤ f(a).
"""

from kdrag import Theorem, define
from kdrag.smt import And, ArraySort, BoolSort, Consts, Exists, ForAll, Lambda, Not, Or
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import ZFSet, elem, le, sep
from kdrag.contrib.zf.fun import bij_on, maps_to
from kdrag.contrib.zf.finite import inv, inv_elem
from kdrag.contrib.zf.poset import (
    exists_least,
    is_least,
    is_partial_order,
    is_total_order,
    is_well_order,
    partial_order_antisymm,
    partial_order_of_well_order,
    seg,
    total_order_of_well_order,
)

X, Y, a, b, x, y = Consts("X Y a b x y", ZFSet)
R, S = Consts("R S", ArraySort(ZFSet, ZFSet, BoolSort()))
f, g, h = Consts("f g h", ArraySort(ZFSet, ZFSet))

# f preserves and reflects the order: a ≤ b iff f(a) ≤ f(b).
is_order_embedding = define(
    "is_order_embedding",
    [f, R, X, S, Y],
    And(
        maps_to(f, X, Y),
        ForAll([a, b], elem(a, X), elem(b, X), R[a, b] == S[f[a], f[b]]),
    ),
)
is_similarity = define(
    "is_similarity",
    [f, R, X, S, Y],
    And(is_order_embedding(f, R, X, S, Y), bij_on(f, X, Y)),
)
similar = define("similar", [R, X, S, Y], Exists(f, is_similarity(f, R, X, S, Y)))


@Theorem(
    ForAll(
        [f, R, X],
        is_well_order(R, X),
        is_order_embedding(f, R, X, R, X),
        ForAll(a, elem(a, X), R[a, f[a]]),
    )
)
def le_apply_of_order_embedding(l):
    """Halmos: if f is a similarity of a well ordered set X into itself, a ≤ f(a)."""
    f, R, X = l.fixes()
    l.intros()
    l.have(is_partial_order(R, X), by=[partial_order_of_well_order(R, X)])
    l.have(
        ForAll([a, b], elem(a, X), elem(b, X), Or(R[a, b], R[b, a])),
        by=[total_order_of_well_order(R, X), is_total_order.defn(R, X)],
    )
    l.have(maps_to(f, X, X), by=[is_order_embedding.defn(f, R, X, R, X)])
    l.have(
        ForAll([a, b], elem(a, X), elem(b, X), R[a, b] == R[f[a], f[b]]),
        by=[is_order_embedding.defn(f, R, X, R, X)],
    )
    a0 = l.fix()
    l.intro()
    l.contra()
    # Otherwise there is a least b with f(b) < b ...
    E = sep(X, Lambda(x, Not(R[x, f[x]])))
    l.have(E <= X, by=[le.defn, zf.elem_sep])
    l.have(elem(a0, E))
    l.rw(zf.elem_sep)
    l.simp()
    l.auto()
    l.have(E != zf.emp, by=[zf.elem_emp(a0)])
    l.have(Exists(b, is_least(R, E, b)), by=[exists_least(R, X, E)])
    b0, _ = l.obtain(-1)
    l.have(elem(b0, E), by=[is_least.defn(R, E, b0)])
    l.have(And(elem(b0, X), Not(R[b0, f[b0]])))
    l.have(elem(b0, E) == And(Not(R[b0, f[b0]]), elem(b0, X)))
    l.rw(zf.elem_sep)
    l.simp()
    l.auto()
    l.auto()
    fb = f[b0]
    l.have(elem(fb, X), by=[maps_to.defn(f, X, X)])
    l.have(R[fb, b0])
    l.auto()
    l.have(fb != b0)
    l.auto()
    # ... then f(f(b)) < f(b) since f preserves the order, so f(b) is in E and below b.
    l.have(Not(R[fb, f[fb]]))
    l.intro()
    l.have(R[f[fb], fb])
    l.auto()
    l.have(
        f[fb] == fb, by=[partial_order_antisymm(R, X, f[fb], fb), maps_to.defn(f, X, X)]
    )
    l.auto(by=[partial_order_antisymm(R, X, fb, b0)])
    l.have(elem(fb, E))
    l.rw(zf.elem_sep)
    l.simp()
    l.auto()
    l.auto(by=[is_least.defn(R, E, b0), partial_order_antisymm(R, X, fb, b0)])


def _sims(g, h, R, X, S, Y):
    return [
        is_well_order(R, X),
        is_well_order(S, Y),
        is_similarity(g, R, X, S, Y),
        is_similarity(h, R, X, S, Y),
    ]


@Theorem(
    ForAll(
        [g, h, R, X, S, Y],
        *_sims(g, h, R, X, S, Y),
        ForAll(a, elem(a, X), S[g[a], h[a]]),
    )
)
def le_of_similarities(l):
    """Halmos: g⁻¹h is a similarity of X into itself, so a ≤ g⁻¹(h(a)), and g(a) ≤ h(a)."""
    g, h, R, X, S, Y = l.fixes()
    l.intros()
    gi = inv(g, X)
    k = Lambda(x, gi[h[x]])
    l.have(bij_on(g, X, Y), by=[is_similarity.defn(g, R, X, S, Y)])
    l.have(
        ForAll(y, elem(y, Y), And(elem(gi[y], X), g[gi[y]] == y)),
        by=[inv_elem],
    )
    l.have(
        maps_to(h, X, Y),
        by=[is_similarity.defn(h, R, X, S, Y), is_order_embedding.defn],
    )
    l.have(is_order_embedding(k, R, X, R, X))
    l.unfold(is_order_embedding)
    l.split()
    l.auto(by=[maps_to.defn(h, X, Y), maps_to.defn(k, X, X)])
    # a ≤ b iff h(a) ≤ h(b) iff g(g⁻¹h(a)) ≤ g(g⁻¹h(b)) iff g⁻¹h(a) ≤ g⁻¹h(b).
    a1, b1 = l.fixes()
    l.intros()
    l.auto(
        by=[
            is_similarity.defn(g, R, X, S, Y),
            is_similarity.defn(h, R, X, S, Y),
            is_order_embedding.defn(g, R, X, S, Y),
            is_order_embedding.defn(h, R, X, S, Y),
            maps_to.defn(h, X, Y),
        ]
    )
    l.have(ForAll(a, elem(a, X), R[a, k[a]]), by=[le_apply_of_order_embedding(k, R, X)])
    l.fix()
    l.intro()
    l.auto(
        by=[
            is_similarity.defn(g, R, X, S, Y),
            is_order_embedding.defn(g, R, X, S, Y),
            maps_to.defn(h, X, Y),
        ]
    )


@Theorem(
    ForAll(
        [g, h, R, X, S, Y],
        *_sims(g, h, R, X, S, Y),
        ForAll(a, elem(a, X), g[a] == h[a]),
    )
)
def similarity_unique(l):
    """Halmos: two well ordered sets have at most one similarity between them."""
    g, h, R, X, S, Y = l.fixes()
    l.intros()
    a0 = l.fix()
    l.intro()
    # g(a) ≤ h(a) and h(a) ≤ g(a), so they are equal by antisymmetry in Y.
    l.auto(
        by=[
            le_of_similarities(g, h, R, X, S, Y),
            le_of_similarities(h, g, R, X, S, Y),
            partial_order_antisymm(S, Y, g[a0], h[a0]),
            partial_order_of_well_order(S, Y),
            is_similarity.defn,
            is_order_embedding.defn,
            maps_to.defn,
        ]
    )


@Theorem(
    ForAll(
        [f, R, X, a],
        is_well_order(R, X),
        elem(a, X),
        Not(is_similarity(f, R, X, R, seg(R, X, a))),
    )
)
def not_similarity_seg(l):
    """Halmos: a well ordered set is never similar to one of its initial segments."""
    f, R, X, a0 = l.fixes()
    l.intros()
    l.intro()
    sa = seg(R, X, a0)
    l.have(sa <= X, by=[seg.defn, zf.elem_sep, le.defn])
    # f maps X into s(a) ⊆ X preserving the order, so a ≤ f(a), but f(a) < a.
    l.have(is_order_embedding(f, R, X, R, X))
    l.unfold(is_order_embedding)
    l.auto(
        by=[
            is_similarity.defn(f, R, X, R, sa),
            is_order_embedding.defn(f, R, X, R, sa),
            maps_to.defn,
            le.defn,
        ]
    )
    l.have(R[a0, f[a0]], by=[le_apply_of_order_embedding(f, R, X)])
    l.have(
        elem(f[a0], sa),
        by=[
            is_similarity.defn(f, R, X, R, sa),
            is_order_embedding.defn(f, R, X, R, sa),
            maps_to.defn(f, X, sa),
        ],
    )
    l.have(And(R[f[a0], a0], f[a0] != a0, elem(f[a0], X)))
    l.unfold(seg, at=-1)
    l.rw(zf.elem_sep, at=-1)
    l.simp(at=-1)
    l.auto()
    l.auto(
        by=[partial_order_antisymm(R, X, a0, f[a0]), partial_order_of_well_order(R, X)]
    )
