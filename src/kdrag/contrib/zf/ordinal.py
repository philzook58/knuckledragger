"""
Ordinal numbers (Halmos §19) and the axiom of substitution (Replacement).

Halmos: an ordinal number is a well ordered set α such that s(ξ) = ξ for every
ξ ∈ α. With s(ξ) = {η ∈ α | η < ξ}, the order is forced to be "∈ or =", the
same relation `nat_le` that orders ω.
"""

from kdrag import Theorem, axiom, define, prove
from kdrag.smt import And, ArraySort, Consts, Exists, ForAll, Function, Not, Or
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import ZFSet, elem, le, succ
from kdrag.contrib.zf.fun import maps_to
from kdrag.contrib.zf.finite import image
from kdrag.contrib.zf.nat import elem_succ, is_transitive, omega
from kdrag.contrib.zf.order import nat_le
from kdrag.contrib.zf.poset import (
    R,
    exists_least,
    partial_order_antisymm,
    partial_order_of_well_order,
    partial_order_trans,
    is_least,
    is_partial_order,
    is_well_order,
    nat_le_rel,
    omega_well_order,
    seg,
    seg_nat,
)

A, B, E, a, x, y = Consts("A B E a x y", ZFSet)
F = Consts("F", ArraySort(ZFSet, ZFSet))[0]

# Halmos' axiom of substitution, in HOL form: the image of a set under any
# function is a set. This is the second axiom of contrib.zf, after infinity.
repl = Function("repl", ArraySort(ZFSet, ZFSet), ZFSet, ZFSet)
elem_repl = axiom(
    ForAll([F, A, y], elem(y, repl(F, A)) == Exists(x, And(elem(x, A), F[x] == y)))
)


# With Replacement the image no longer needs a known codomain.
@Theorem(ForAll([F, A, B], maps_to(F, A, B), image(F, A, B) == repl(F, A)))
def image_eq_repl(l):
    F, A, B = l.fixes()
    l.intro()
    l.unfold(image)
    l.rw(zf.ext_ax)
    y0 = l.fix()
    l.rw(zf.elem_sep)
    l.simp()
    # Values F x with x ∈ A already lie in B.
    l.auto(by=[elem_repl(F, A, y0), maps_to.defn(F, A, B)])


# Ordinal numbers

is_ordinal = define(
    "is_ordinal",
    [A],
    And(
        is_well_order(nat_le_rel, A),
        ForAll(x, elem(x, A), seg(nat_le_rel, A, x) == x),
    ),
)

elem_seg = prove(
    ForAll(
        [A, a, y],
        elem(y, seg(nat_le_rel, A, a))
        == And(elem(y, A), Or(elem(y, a), y == a), y != a),
    ),
    by=[seg.defn, zf.elem_sep, nat_le.defn],
)


@Theorem(
    ForAll(
        A,
        is_ordinal(A)
        == And(
            is_well_order(nat_le_rel, A),
            is_transitive(A),
            ForAll(x, elem(x, A), Not(elem(x, x))),
        ),
    )
)
def is_ordinal_iff(l):
    """s(ξ) = ξ for all ξ ∈ α says exactly that α is transitive and ξ ∉ ξ."""
    A = l.fix()
    l.unfold(is_ordinal)
    l.split()
    # → : ξ = s(ξ) ⊆ α, and ξ ∉ s(ξ) = ξ.
    l.intro()
    l.split()
    l.auto()
    l.unfold(is_transitive)
    x0 = l.fix()
    l.intro()
    l.unfold(le)
    y0 = l.fix()
    l.intro()
    l.auto(by=[elem_seg(A, x0, y0)])
    x1 = l.fix()
    l.intros()
    l.auto(by=[elem_seg(A, x1, x1)])
    # ← : for ξ ∈ α, η ∈ s(ξ) iff η ∈ ξ, by transitivity and ξ ∉ ξ.
    l.intro()
    l.split()
    l.auto()
    x2 = l.fix()
    l.intro()
    l.rw(zf.ext_ax)
    y0 = l.fix()
    l.auto(by=[elem_seg(A, x2, y0), is_transitive.defn(A), le.defn])


omega_is_ordinal = prove(
    is_ordinal(omega), by=[is_ordinal.defn, omega_well_order, seg_nat]
)


@Theorem(ForAll([R, A, B], is_well_order(R, A), B <= A, is_well_order(R, B)))
def well_order_subset(l):
    """A subset of a well ordered set is well ordered."""
    R, A, B = l.fixes()
    l.intros()
    l.unfold(is_well_order)
    l.unfold(is_well_order, at=0)
    l.split()
    l.auto(by=[is_partial_order.defn(R, A), is_partial_order.defn(R, B), le.defn])
    l.fix()
    l.intros()
    l.auto(by=[le.defn])


@Theorem(ForAll([A, a], is_ordinal(A), elem(a, A), is_ordinal(a)))
def is_ordinal_of_elem(l):
    """Halmos: every element of an ordinal number is an ordinal number."""
    A, a = l.fixes()
    l.intros()
    l.rw(is_ordinal_iff, at=0)
    l.rw(is_ordinal_iff)
    l.split(at=0)
    l.have(a <= A, by=[is_transitive.defn, le.defn])
    l.split()
    l.auto(by=[well_order_subset(nat_le_rel, A, a)])
    # ζ ∈ η ∈ ξ in α gives ζ ≤ ξ by transitivity of the order; ζ = ξ would give
    # ξ ∈ η ∈ ξ, so ξ = η by antisymmetry and ξ ∈ ξ.
    l.unfold(is_transitive)
    y0 = l.fix()
    l.intro()
    l.unfold(le)
    z0 = l.fix()
    l.intro()
    l.have(elem(y0, A), by=[le.defn(a, A)])
    l.have(elem(z0, A), by=[is_transitive.defn(A), le.defn(y0, A)])
    l.have(is_partial_order(nat_le_rel, A), by=[partial_order_of_well_order])
    l.have(
        nat_le(z0, a),
        by=[partial_order_trans(nat_le_rel, A, z0, y0, a), nat_le.defn],
    )
    l.auto(
        by=[
            nat_le.defn,
            partial_order_antisymm(nat_le_rel, A, a, y0),
        ]
    )
    l.auto(by=[le.defn])


nat_is_ordinal = prove(
    ForAll(a, elem(a, omega), is_ordinal(a)),
    by=[is_ordinal_of_elem, omega_is_ordinal],
)


# Stated on its own: inside `is_ordinal_succ` the unused hypothesis
# is_well_order(λ, α) made this step seed-dependent (see the issue tracker).
@Theorem(
    ForAll(
        [E, A],
        E <= succ(A),
        E & A == zf.emp,
        ForAll(x, elem(x, E), x == A),
    )
)
def eq_of_le_succ_of_inter_emp(l):
    E, A = l.fixes()
    l.intros()
    x0 = l.fix()
    l.intro()
    # x ∈ α⁺ means x ∈ α or x = α, and x ∈ α would put x in E ∩ α = ∅.
    l.have(elem(x0, succ(A)), by=[le.defn(E, succ(A))])
    l.have(Not(elem(x0, E & A)), by=[zf.elem_emp(x0)])
    l.auto(by=[zf.elem_inter(x0, E, A), elem_succ(x0, A)])


@Theorem(ForAll(A, is_ordinal(A), is_ordinal(succ(A))))
def is_ordinal_succ(l):
    """Halmos: the successor α⁺ = α ∪ {α} of an ordinal is an ordinal, with α last."""
    A = l.fix()
    l.intro()
    l.rw(is_ordinal_iff, at=0)
    l.split(at=0)
    l.have(Not(elem(A, A)))
    l.intro()
    l.auto()
    l.rw(is_ordinal_iff)
    l.split()

    # The order: elements of α⁺ are elements of α or α itself, and α is above all of α.
    l.unfold(is_well_order)
    l.split()
    l.unfold(is_partial_order)
    l.split()
    l.auto(by=[nat_le.defn])
    l.have(is_partial_order(nat_le_rel, A), by=[partial_order_of_well_order])
    # Antisymmetry: both in α is α's antisymmetry; α ∈ y ∈ α would put α ∈ α.
    x0, y0 = l.fixes()
    l.intros()
    l.auto(
        by=[
            elem_succ(x0, A),
            elem_succ(y0, A),
            nat_le.defn,
            partial_order_antisymm(nat_le_rel, A, x0, y0),
            is_transitive.defn(A),
            le.defn(x0, A),
            le.defn(y0, A),
        ]
    )
    # Transitivity: everything is ≤ α, and below an element of α we stay in α.
    x1, y1, z1 = l.fixes()
    l.intros()
    l.auto(
        by=[
            elem_succ(x1, A),
            elem_succ(y1, A),
            elem_succ(z1, A),
            nat_le.defn,
            partial_order_trans(nat_le_rel, A, x1, y1, z1),
            partial_order_of_well_order(nat_le_rel, A),
            le.defn(x1, A),
            is_transitive.defn(A),
            le.defn(y1, A),
            le.defn(z1, A),
        ]
    )
    # A nonempty E ⊆ α⁺ has a least element: the least of E ∩ α if that is
    # nonempty, and α otherwise.
    E0 = l.fix()
    l.intros()
    l.cases(E0 & A != zf.emp, E0 & A == zf.emp)
    l.have(E0 & A <= A, by=[le.defn, zf.elem_inter])
    l.have(
        Exists(a, is_least(nat_le_rel, E0 & A, a)),
        by=[exists_least(nat_le_rel, A, E0 & A)],
    )
    a0, _ = l.obtain(-1)
    l.exists(a0)
    l.auto(by=[is_least.defn, zf.elem_inter, le.defn, elem_succ, nat_le.defn])
    # E ∩ α = ∅: every element of E is α itself, and E has one.
    l.exists(A)
    l.have(ForAll(x, elem(x, E0), x == A), by=[eq_of_le_succ_of_inter_emp(E0, A)])
    l.have(Exists(x, elem(x, E0)), by=[zf.not_emp_exists_elem(E0)])
    l.auto(by=[is_least.defn(nat_le_rel, E0, A), nat_le.defn])

    # α⁺ is transitive: α ⊆ α⁺, and elements of α are subsets of α.
    l.auto(by=[is_transitive.defn, le.defn, elem_succ])
    # No element of α⁺ is a member of itself.
    l.auto(by=[elem_succ])
