"""
Partially ordered sets (Halmos §14), and well-orderings (Halmos §17).

A relation in X is a HOL predicate `R[x, y]` considered on elements of X,
just as one-to-one correspondences are HOL functions.
"""

from kdrag import Theorem, define, prove
from kdrag.smt import And, ArraySort, BoolSort, Consts, Exists, ForAll, Lambda, Not, Or
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import ZFSet, elem, le, pow, sep
from kdrag.contrib.zf.nat import nat_not_elem_self, omega
from kdrag.contrib.zf.order import (
    exists_least_of_nonempty,
    nat_le,
    nat_le_antisymm,
    nat_le_trans,
    nat_of_elem,
)

E, X, a, b, x, y, z = Consts("E X a b x y z", ZFSet)
R = Consts("R", ArraySort(ZFSet, ZFSet, BoolSort()))[0]

is_partial_order = define(
    "is_partial_order",
    [R, X],
    And(
        ForAll(x, elem(x, X), R[x, x]),
        ForAll([x, y], elem(x, X), elem(y, X), R[x, y], R[y, x], x == y),
        ForAll(
            [x, y, z], elem(x, X), elem(y, X), elem(z, X), R[x, y], R[y, z], R[x, z]
        ),
    ),
)
is_total_order = define(
    "is_total_order",
    [R, X],
    And(
        is_partial_order(R, X),
        ForAll([x, y], elem(x, X), elem(y, X), Or(R[x, y], R[y, x])),
    ),
)

# a is the least element of E: a ∈ E and a ≤ x for all x ∈ E.
is_least = define(
    "is_least", [R, E, a], And(elem(a, E), ForAll(x, elem(x, E), R[a, x]))
)
# a is minimal in E: no element of E is strictly below a.
is_minimal = define(
    "is_minimal",
    [R, E, a],
    And(elem(a, E), ForAll(x, elem(x, E), R[x, a], x == a)),
)

# Halmos §17: a well ordering is a partial order in which every nonempty subset
# has a least element.
is_well_order = define(
    "is_well_order",
    [R, X],
    And(
        is_partial_order(R, X),
        ForAll(E, E <= X, E != zf.emp, Exists(a, is_least(R, E, a))),
    ),
)

# The order laws one at a time, for instantiating in proofs.
partial_order_of_well_order = prove(
    ForAll([R, X], is_well_order(R, X), is_partial_order(R, X)),
    by=[is_well_order.defn],
)
partial_order_antisymm = prove(
    ForAll(
        [R, X, x, y],
        is_partial_order(R, X),
        elem(x, X),
        elem(y, X),
        R[x, y],
        R[y, x],
        x == y,
    ),
    by=[is_partial_order.defn],
)
partial_order_trans = prove(
    ForAll(
        [R, X, x, y, z],
        is_partial_order(R, X),
        elem(x, X),
        elem(y, X),
        elem(z, X),
        R[x, y],
        R[y, z],
        R[x, z],
    ),
    by=[is_partial_order.defn],
)
exists_least = prove(
    ForAll(
        [R, X, E],
        is_well_order(R, X),
        E <= X,
        E != zf.emp,
        Exists(a, is_least(R, E, a)),
    ),
    by=[is_well_order.defn],
)

# The initial segment s(a) = {x ∈ X | x < a}.
seg = define("seg", [R, X, a], sep(X, Lambda(x, And(R[x, a], x != a))))


subset_rel = Lambda([x, y], x <= y)


@Theorem(ForAll(X, is_partial_order(subset_rel, pow(X))))
def subset_partial_order(l):
    """Halmos: inclusion is a partial order in the power set."""
    l.fix()
    l.unfold(is_partial_order)
    l.split()
    l.auto(by=[le.defn])
    # Antisymmetry is extensionality.
    l.auto(by=[le.defn, zf.ext_ax])
    l.auto(by=[le.defn])


# The antisymmetry of an order makes least elements unique.
least_unique = prove(
    ForAll(
        [R, X, E, a, b],
        is_partial_order(R, X),
        E <= X,
        is_least(R, E, a),
        is_least(R, E, b),
        a == b,
    ),
    by=[is_partial_order.defn, is_least.defn, le.defn],
)

# A least element is minimal; Halmos' nonempty subsets show the converse fails.
minimal_of_least = prove(
    ForAll(
        [R, X, E, a],
        is_partial_order(R, X),
        E <= X,
        is_least(R, E, a),
        is_minimal(R, E, a),
    ),
    by=[is_partial_order.defn, is_least.defn, is_minimal.defn, le.defn],
)


@Theorem(ForAll([R, X], is_well_order(R, X), is_total_order(R, X)))
def total_order_of_well_order(l):
    """Halmos §17: a well ordering is total, since {x, y} has a least element."""
    R, X = l.fixes()
    l.intro()
    l.unfold(is_total_order)
    l.split()
    l.auto(by=[is_well_order.defn])
    x, y = l.fixes()
    l.intros()
    l.have(zf.upair(x, y) <= X, by=[le.defn, zf.elem_upair])
    l.have(zf.upair(x, y) != zf.emp, by=[zf.upair_not_emp])
    l.have(Exists(a, is_least(R, zf.upair(x, y), a)), by=[is_well_order.defn])
    a0, _ = l.obtain(-1)
    l.auto(by=[is_least.defn(R, zf.upair(x, y), a0), zf.elem_upair])


nat_le_rel = Lambda([x, y], nat_le(x, y))


@Theorem(is_well_order(nat_le_rel, omega))
def omega_well_order(l):
    """ω is well ordered by ≤ (Halmos §13 exercise, in the language of §17)."""
    l.unfold(is_well_order)
    l.split()
    l.unfold(is_partial_order)
    l.split()
    l.auto(by=[nat_le.defn])
    l.auto(by=[nat_le_antisymm])
    l.auto(by=[nat_le_trans])
    # Every nonempty set of naturals has a least element.
    E = l.fix()
    l.intros()
    l.have(
        Exists(a, And(elem(a, E), ForAll(x, elem(x, E), nat_le(a, x)))),
        by=[exists_least_of_nonempty(E)],
    )
    k, _ = l.obtain(-1)
    l.exists(k)
    l.auto(by=[is_least.defn(nat_le_rel, E, k)])


@Theorem(ForAll(a, elem(a, omega), seg(nat_le_rel, omega, a) == a))
def seg_nat(l):
    """Each natural number is the initial segment of its predecessors."""
    n = l.fix()
    l.intro()
    l.unfold(seg)
    l.rw(zf.ext_ax)
    z = l.fix()
    l.rw(zf.elem_sep)
    l.simp()
    # z < n in ω means z ∈ n, and elements of n are natural numbers.
    l.auto(by=[nat_le.defn(z, n), nat_of_elem(z, n), nat_not_elem_self(n)])


P = Consts("P", ArraySort(ZFSet, BoolSort()))[0]


@Theorem(
    ForAll(
        [R, X, P],
        is_well_order(R, X),
        ForAll(a, elem(a, X), ForAll(b, elem(b, seg(R, X, a)), P[b]), P[a]),
        ForAll(a, elem(a, X), P[a]),
    )
)
def well_order_induction(l):
    """Halmos §17, the principle of transfinite induction: if all predecessors of x
    having a property forces x to have it, then every element has it."""
    R, X, P = l.fixes()
    l.intros()
    a0 = l.fix()
    l.intro()
    l.contra()
    # Otherwise the elements without the property have a least one, a.
    Bad = sep(X, Lambda(x, Not(P[x])))
    l.have(Bad <= X, by=[le.defn, zf.elem_sep])
    l.have(Bad != zf.emp, by=[zf.elem_sep(Lambda(x, Not(P[x])), X, a0), zf.elem_emp])
    l.have(Exists(a, is_least(R, Bad, a)), by=[exists_least(R, X, Bad)])
    a1, _ = l.obtain(-1)
    l.have(elem(a1, X), by=[is_least.defn(R, Bad, a1), zf.elem_sep, le.defn])
    # Every b < a has the property: otherwise b ∈ Bad and a ≤ b < a.
    l.have(ForAll(b, elem(b, seg(R, X, a1)), P[b]))
    b0 = l.fix()
    l.intros()
    l.contra()
    l.auto(
        by=[
            seg.defn(R, X, a1),
            zf.elem_sep,
            is_least.defn(R, Bad, a1),
            partial_order_antisymm(R, X, a1, b0),
            partial_order_of_well_order(R, X),
        ]
    )
    # So a has the property, but a ∈ Bad.
    l.auto(by=[is_least.defn(R, Bad, a1), zf.elem_sep])
