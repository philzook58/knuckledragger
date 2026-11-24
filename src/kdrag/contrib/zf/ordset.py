"""
Sets of ordinal numbers and the counting theorem (Halmos §20).

Similar ordinals are equal, any two ordinals are comparable, a transitive set
of ordinals is an ordinal, and every well ordered set is similar to a unique
ordinal. The counting theorem uses Replacement and definite description.
"""

from kdrag import Theorem, define, prove
from kdrag.smt import And, ArraySort, Consts, Exists, ForAll, Implies, Lambda, Not, Or
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import ZFSet, bigunion, elem, le, succ
from kdrag.contrib.zf.fun import bij_on, elem_sub, inj_on, maps_to, surj_on
from kdrag.contrib.zf.nat import elem_succ_self, is_transitive
from kdrag.contrib.zf.order import nat_le
from kdrag.contrib.zf.ordinal import (
    elem_seg,
    is_ordinal,
    is_ordinal_iff,
    is_ordinal_of_elem,
    is_ordinal_succ,
    well_order_subset,
)
from kdrag.contrib.zf.poset import (
    exists_least,
    is_least,
    is_partial_order,
    is_total_order,
    is_well_order,
    nat_le_rel,
    partial_order_antisymm,
    partial_order_of_well_order,
    seg,
    total_order_of_well_order,
    well_order_induction,
)
from kdrag.contrib.zf.sim import is_order_embedding, is_similarity

A, B, a, b, x, y, z = Consts("A B a b x y z", ZFSet)
f = Consts("f", ArraySort(ZFSet, ZFSet))[0]

# The three parts of `is_ordinal_iff`, one at a time.
ordinal_well_order = prove(
    ForAll(A, is_ordinal(A), is_well_order(nat_le_rel, A)), by=[is_ordinal_iff]
)
ordinal_le_of_elem = prove(
    ForAll([A, x], is_ordinal(A), elem(x, A), x <= A),
    by=[is_ordinal_iff, is_transitive.defn],
)
ordinal_not_elem_self = prove(
    ForAll([A, x], is_ordinal(A), elem(x, A), Not(elem(x, x))), by=[is_ordinal_iff]
)


@Theorem(
    ForAll(
        [f, A, B],
        is_ordinal(A),
        is_ordinal(B),
        is_similarity(f, nat_le_rel, A, nat_le_rel, B),
        A == B,
    )
)
def eq_of_similarity(l):
    """Halmos §20: for ordinal numbers similarity is the same as equality."""
    f, A, B = l.fixes()
    l.intros()
    sim_defs = [
        is_similarity.defn(f, nat_le_rel, A, nat_le_rel, B),
        is_order_embedding.defn(f, nat_le_rel, A, nat_le_rel, B),
    ]
    l.have(maps_to(f, A, B), by=sim_defs)
    l.have(bij_on(f, A, B), by=sim_defs)
    l.have(
        ForAll([a, b], elem(a, A), elem(b, A), nat_le(a, b) == nat_le(f[a], f[b])),
        by=sim_defs,
    )
    # Keep only the extracted facts: the similarity hypothesis carries the lambda
    # order and slows later steps down (see the issue tracker).
    l.clear(is_similarity(f, nat_le_rel, A, nat_le_rel, B))
    # By transfinite induction f is the identity: f(ξ) = {f(η) | η < ξ} = {η | η < ξ} = ξ.
    l.have(ForAll(a, elem(a, A), f[a] == a))
    l.have(
        ForAll(
            a,
            elem(a, A),
            ForAll(b, elem(b, seg(nat_le_rel, A, a)), f[b] == b),
            f[a] == a,
        )
    )
    a0 = l.fix()
    l.intros()
    l.rw(zf.ext_ax)
    y0 = l.fix()
    l.split()
    # η ∈ f(ξ): η ∈ β, so η = f(ζ) with ζ < ξ, and f(ζ) = ζ.
    l.intro()
    l.have(elem(f[a0], B), by=[maps_to.defn(f, A, B)])
    l.have(elem(y0, B), by=[ordinal_le_of_elem(B, f[a0]), le.defn])
    l.have(
        Exists(x, And(elem(x, A), f[x] == y0)),
        by=[bij_on.defn(f, A, B), surj_on.defn(f, A, B)],
    )
    z0, _ = l.obtain(-1)
    l.auto(
        by=[
            nat_le.defn,
            elem_seg(A, a0, z0),
            ordinal_not_elem_self(B, f[a0]),
        ]
    )
    # η ∈ ξ: η < ξ, so f(η) = η ≤ f(ξ), and f(η) = f(ξ) would give η = ξ ∈ ξ.
    l.intro()
    l.have(elem(y0, A), by=[ordinal_le_of_elem(A, a0), le.defn])
    l.have(
        elem(y0, seg(nat_le_rel, A, a0)),
        by=[elem_seg(A, a0, y0), ordinal_not_elem_self(A, a0)],
    )
    l.have(f[y0] == y0)
    l.auto()
    l.have(nat_le(f[y0], f[a0]), by=[nat_le.defn(y0, a0)])
    l.auto(
        by=[
            nat_le.defn(f[y0], f[a0]),
            inj_on.defn(f, A),
            bij_on.defn(f, A, B),
            ordinal_not_elem_self(A, a0),
        ]
    )
    l.auto(
        by=[
            well_order_induction(nat_le_rel, A, Lambda(x, f[x] == x)),
            ordinal_well_order(A),
        ]
    )
    # So α = f[α] = β.
    l.rw(zf.ext_ax)
    l.fix()
    l.auto(by=[maps_to.defn(f, A, B), bij_on.defn(f, A, B), surj_on.defn(f, A, B)])


@Theorem(ForAll([A, B], is_ordinal(A), is_ordinal(B), is_ordinal(A & B)))
def is_ordinal_inter(l):
    A, B = l.fixes()
    l.intros()
    l.rw(is_ordinal_iff)
    l.split()
    l.auto(
        by=[
            well_order_subset(nat_le_rel, A, A & B),
            ordinal_well_order(A),
            le.defn,
            zf.elem_inter,
        ]
    )
    # Elements of α ∩ β are subsets of both.
    l.unfold(is_transitive)
    x0 = l.fix()
    l.intro()
    l.auto(
        by=[
            ordinal_le_of_elem(A, x0),
            ordinal_le_of_elem(B, x0),
            zf.elem_inter,
            le.defn,
        ]
    )
    l.auto(by=[ordinal_not_elem_self, zf.elem_inter])


@Theorem(
    ForAll(
        [A, x, y],
        is_ordinal(A),
        elem(x, A),
        elem(y, A),
        Or(elem(x, y), x == y, elem(y, x)),
    )
)
def ordinal_total(l):
    """Elements of an ordinal are comparable: its well order is total."""
    A, x0, y0 = l.fixes()
    l.intros()
    l.have(
        is_total_order(nat_le_rel, A),
        by=[total_order_of_well_order(nat_le_rel, A), ordinal_well_order(A)],
    )
    l.have(
        Or(nat_le_rel[x0, y0], nat_le_rel[y0, x0]),
        by=[is_total_order.defn(nat_le_rel, A)],
    )
    l.simp(at=-1)
    l.auto(by=[nat_le.defn(x0, y0), nat_le.defn(y0, x0)])


@Theorem(
    ForAll(
        [A, B],
        is_ordinal(A),
        is_transitive(B),
        B <= A,
        B != A,
        elem(B, A),
    )
)
def elem_of_transitive_ssubset(l):
    """A transitive proper subset of an ordinal is one of its elements: the least
    element of α - β."""
    A, B = l.fixes()
    l.intros()
    D = A - B
    l.have(D <= A, by=[le.defn, elem_sub])
    l.have(D != zf.emp, by=[zf.ext_ax(B, A), le.defn, elem_sub, zf.elem_emp])
    l.have(
        Exists(a, is_least(nat_le_rel, D, a)),
        by=[exists_least(nat_le_rel, A, D), ordinal_well_order(A)],
    )
    c0, _ = l.obtain(-1)
    l.have(
        And(elem(c0, A), Not(elem(c0, B))),
        by=[is_least.defn(nat_le_rel, D, c0), elem_sub],
    )
    # ξ = β: below ξ everything is in β, and an element of β above ξ would put ξ in β.
    l.have(c0 == B)
    l.rw(zf.ext_ax)
    y0 = l.fix()
    l.split()
    l.intro()
    l.have(elem(y0, A), by=[ordinal_le_of_elem(A, c0), le.defn])
    # η ∉ β would put η in α - β below its least element ξ.
    l.have(
        Implies(Not(elem(y0, B)), nat_le(c0, y0)),
        by=[is_least.defn(nat_le_rel, D, c0), elem_sub(y0, A, B)],
    )
    l.auto(
        by=[
            nat_le.defn(c0, y0),
            nat_le.defn(y0, c0),
            partial_order_antisymm(nat_le_rel, A, c0, y0),
            partial_order_of_well_order(nat_le_rel, A),
            ordinal_well_order(A),
            ordinal_not_elem_self(A, c0),
        ]
    )
    l.intro()
    l.auto(
        by=[
            le.defn(B, A),
            ordinal_total(A, y0, c0),
            is_transitive.defn(B),
            le.defn(y0, B),
        ]
    )
    l.auto()


@Theorem(
    ForAll([A, B], is_ordinal(A), is_ordinal(B), Or(elem(A, B), A == B, elem(B, A)))
)
def ordinal_comparable(l):
    """Halmos §20: any two ordinal numbers are comparable."""
    A, B = l.fixes()
    l.intros()
    C = A & B
    l.have(is_ordinal(C), by=[is_ordinal_inter(A, B)])
    l.have(is_transitive(C), by=[is_ordinal_iff(C)])
    l.have(And(C <= A, C <= B), by=[le.defn, zf.elem_inter])
    # α ∩ β is α, or β, or an element of both; the last would put it in itself.
    l.have(Or(C == A, elem(C, A)), by=[elem_of_transitive_ssubset(A, C)])
    l.have(Or(C == B, elem(C, B)), by=[elem_of_transitive_ssubset(B, C)])
    l.have(
        Not(And(elem(C, A), elem(C, B))),
        by=[zf.elem_inter, ordinal_not_elem_self(A, C)],
    )
    l.auto(by=[zf.ext_ax(A, B), le.defn, zf.elem_inter])


E, e, m = Consts("E e m", ZFSet)


@Theorem(
    ForAll(
        [A, E],
        ForAll(x, elem(x, A), is_ordinal(x)),
        E <= A,
        E != zf.emp,
        Exists(m, is_least(nat_le_rel, E, m)),
    )
)
def exists_least_of_ordinals(l):
    """A nonempty set of ordinals has a least element: some e ∈ E, or else the least
    element of e ∩ E in the ordinal e."""
    A, E = l.fixes()
    l.intros()
    l.have(Exists(e, elem(e, E)), by=[zf.not_emp_exists_elem(E)])
    e0, _ = l.obtain(-1)
    l.have(is_ordinal(e0), by=[le.defn])
    D = e0 & E
    l.cases(D == zf.emp, D != zf.emp)
    # e ∩ E = ∅: nothing in E lies below e, so e is least by comparability.
    l.exists(e0)
    l.have(ForAll(x, elem(x, E), nat_le(e0, x)))
    x0 = l.fix()
    l.intro()
    l.auto(
        by=[
            ordinal_comparable(e0, x0),
            le.defn,
            nat_le.defn(e0, x0),
            zf.ext_ax(D, zf.emp),
            zf.elem_inter,
            zf.elem_emp,
        ]
    )
    l.auto(by=[is_least.defn(nat_le_rel, E, e0)])
    # Otherwise take the least m of e ∩ E in e; anything in E below m lies in e ∩ E.
    l.have(D <= e0, by=[le.defn, zf.elem_inter])
    l.have(
        Exists(m, is_least(nat_le_rel, D, m)),
        by=[exists_least(nat_le_rel, e0, D), ordinal_well_order(e0)],
    )
    m0, _ = l.obtain(-1)
    l.have(
        And(elem(m0, e0), elem(m0, E)),
        by=[is_least.defn(nat_le_rel, D, m0), zf.elem_inter],
    )
    l.exists(m0)
    l.have(ForAll(x, elem(x, E), nat_le(m0, x)))
    x1 = l.fix()
    l.intro()
    l.have(
        Implies(elem(x1, m0), elem(x1, D)),
        by=[ordinal_le_of_elem(e0, m0), le.defn, zf.elem_inter],
    )
    l.have(Implies(elem(x1, D), nat_le(m0, x1)), by=[is_least.defn(nat_le_rel, D, m0)])
    l.auto(
        by=[
            ordinal_comparable(m0, x1),
            le.defn,
            nat_le.defn(m0, x1),
            is_ordinal_of_elem(e0, m0),
            ordinal_le_of_elem(m0, x1),
            ordinal_not_elem_self(m0, m0),
        ]
    )
    l.auto(by=[is_least.defn(nat_le_rel, E, m0)])


@Theorem(
    ForAll(
        A,
        is_transitive(A),
        ForAll(x, elem(x, A), is_ordinal(x)),
        is_ordinal(A),
    )
)
def is_ordinal_of_transitive(l):
    """A transitive set of ordinal numbers is an ordinal number."""
    A = l.fix()
    l.intros()
    l.rw(is_ordinal_iff)
    l.split()
    l.unfold(is_well_order)
    l.split()
    l.unfold(is_partial_order)
    l.split()
    l.auto(by=[nat_le.defn])
    # x ∈ y ∈ x would put y in itself.
    x0, y0 = l.fixes()
    l.intros()
    l.auto(
        by=[
            nat_le.defn,
            ordinal_le_of_elem(y0, x0),
            le.defn,
            ordinal_not_elem_self(y0, y0),
        ]
    )
    # x ∈ y ∈ z gives x ∈ z, as z is transitive.
    x1, y1, z1 = l.fixes()
    l.intros()
    l.auto(by=[nat_le.defn, ordinal_le_of_elem(z1, y1), le.defn])
    E0 = l.fix()
    l.intros()
    l.auto(by=[exists_least_of_ordinals(A, E0)])
    l.auto()
    l.auto(by=[ordinal_not_elem_self])


# Suprema and the Burali-Forti paradox

C = Consts("C", ZFSet)[0]


@Theorem(ForAll(C, ForAll(x, elem(x, C), is_ordinal(x)), is_ordinal(bigunion(C))))
def is_ordinal_bigunion(l):
    """Halmos: the union of a set of ordinal numbers is an ordinal number."""
    C = l.fix()
    l.intro()
    U = bigunion(C)
    # ⋃C is transitive (each member is), and its elements are elements of ordinals.
    l.have(is_transitive(U))
    l.unfold(is_transitive)
    x0 = l.fix()
    l.intro()
    l.have(Exists(B, And(elem(B, C), elem(x0, B))), by=[zf.bigunion_ax(C, x0)])
    B0, _ = l.obtain(-1)
    l.unfold(le)
    z0 = l.fix()
    l.intro()
    l.auto(by=[ordinal_le_of_elem(B0, x0), le.defn, zf.bigunion_ax(C, z0)])
    l.have(ForAll(x, elem(x, U), is_ordinal(x)))
    x1 = l.fix()
    l.intro()
    l.have(Exists(B, And(elem(B, C), elem(x1, B))), by=[zf.bigunion_ax(C, x1)])
    B1, _ = l.obtain(-1)
    l.auto(by=[is_ordinal_of_elem(B1, x1)])
    l.auto(by=[is_ordinal_of_transitive(U)])


le_bigunion = prove(
    ForAll([C, x], elem(x, C), x <= bigunion(C)), by=[le.defn, zf.bigunion_ax]
)
bigunion_le = prove(
    ForAll([C, B], ForAll(x, elem(x, C), x <= B), bigunion(C) <= B),
    by=[le.defn, zf.bigunion_ax],
)


@Theorem(
    ForAll(
        [A, B],
        is_ordinal(A),
        is_ordinal(B),
        elem(B, A) == And(B <= A, B != A),
    )
)
def ordinal_elem_iff_ssubset(l):
    """Halmos: for distinct ordinals, β ∈ α iff β ⊆ α."""
    A, B = l.fixes()
    l.intros()
    l.split()
    l.intro()
    l.auto(by=[ordinal_le_of_elem(A, B), ordinal_not_elem_self(A, B)])
    # Otherwise α ∈ β or α = β by comparability; α ∈ β ⊆ α would put α in α.
    l.intro()
    l.auto(
        by=[
            ordinal_comparable(A, B),
            le.defn(B, A),
            ordinal_not_elem_self(B, A),
        ]
    )


# The ordinals in a set, named so that later steps never see the predicate given
# to sep; with it in view z3 gave up on a trivial step (see #106).
ordinals_in = define("ordinals_in", [C], zf.sep(C, Lambda(x, is_ordinal(x))))


@Theorem(ForAll([C, x], elem(x, ordinals_in(C)) == And(elem(x, C), is_ordinal(x))))
def elem_ordinals_in(l):
    C, x0 = l.fixes()
    l.unfold(ordinals_in)
    l.rw(zf.elem_sep)
    l.simp()
    l.auto()


@Theorem(Not(Exists(C, ForAll(A, is_ordinal(A), elem(A, C)))))
def burali_forti(l):
    """Halmos §20: there is no set of all ordinal numbers. Its supremum would be an
    ordinal, and its successor an ordinal above every ordinal."""
    l.intro()
    C0, _ = l.obtain(-1)
    O = ordinals_in(C0)
    U = bigunion(O)
    l.have(is_ordinal(U), by=[is_ordinal_bigunion(O), elem_ordinals_in])
    l.have(is_ordinal(succ(U)), by=[is_ordinal_succ(U)])
    l.have(elem(succ(U), O), by=[elem_ordinals_in(C0, succ(U))])
    # U⁺ ⊆ ⋃O = U, but U ∈ U⁺.
    l.have(succ(U) <= U, by=[le_bigunion(O, succ(U))])
    l.have(elem(U, U), by=[le.defn(succ(U), U), elem_succ_self(U)])
    l.auto(by=[ordinal_not_elem_self(U, U)])
