"""
von Neumann natural numbers and the Peano axioms (Halmos §11-12).

ω is the smallest successor ("inductive") set. The only new axiom is the
axiom of infinity in Halmos' form. Foundation is not assumed; `n ∉ n` is
proven for natural numbers by induction, as in Halmos.
"""

import kdrag as kd
from kdrag import Theorem, axiom, define, define_const, prove
from kdrag.smt import And, Consts, Exists, ForAll, Implies, Lambda, Not, Or
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import ZFSet, elem, le, sep, succ, zero

A, S, n, m, x, y = Consts("A S n m x y", ZFSet)
P = zf.P

# Successor


elem_succ = prove(
    ForAll([y, x], elem(y, succ(x)) == Or(elem(y, x), y == x)),
    by=[succ.defn, zf.elem_union, zf.elem_sing],
)
elem_succ_self = prove(ForAll(x, elem(x, succ(x))), by=[elem_succ])
le_succ = prove(ForAll(x, x <= succ(x)), by=[le.defn, elem_succ])
# Peano IV: succ x contains x, but nothing is in 0.
succ_ne_zero = prove(ForAll(x, succ(x) != zero), by=[elem_succ_self, zero.defn, zf.elem_emp])


# ω, the smallest successor set

is_inductive = define(
    "is_inductive", [A], And(elem(zero, A), ForAll(x, elem(x, A), elem(succ(x), A)))
)

infinity_ax = axiom(Exists(A, is_inductive(A)))
(inf_set,), inf_set_inductive = kd.tactics.skolem(infinity_ax)

omega = define_const("omega", sep(inf_set, Lambda(n, ForAll(A, is_inductive(A), elem(n, A)))))


# The `n ∈ inf_set` conjunct of the definition is redundant since inf_set is inductive.
elem_omega = prove(
    ForAll(n, elem(n, omega) == ForAll(A, is_inductive(A), elem(n, A))),
    by=[omega.defn, zf.elem_sep, inf_set_inductive],
)
# Every inductive set contains 0 and is closed under succ, so their intersection is too.
omega_inductive = prove(is_inductive(omega), by=[elem_omega, is_inductive.defn])
# Peano I and II
omega_zero = prove(elem(zero, omega), by=[omega_inductive, is_inductive.defn(omega)])
omega_succ = prove(
    ForAll(n, elem(n, omega), elem(succ(n), omega)), by=[omega_inductive, is_inductive.defn(omega)]
)
omega_le_of_inductive = prove(ForAll(A, is_inductive(A), omega <= A), by=[le.defn, elem_omega])


# Peano III, the principle of mathematical induction in Halmos' form.
# S is inductive and all inductive sets contain ω, so S is squeezed to ω.
eq_omega_of_inductive = prove(
    ForAll(S, S <= omega, elem(zero, S), ForAll(n, elem(n, S), elem(succ(n), S)), S == omega),
    by=[is_inductive.defn, omega_le_of_inductive, zf.ext_ax, le.defn],
)


@Theorem(
    ForAll(P, P(zero), ForAll(n, elem(n, omega), P(n), P(succ(n))), ForAll(n, elem(n, omega), P(n)))
)
def omega_induction(l):
    """Induction over ω for any class P, via the set {n ∈ ω | P n}."""
    P = l.fix()
    l.intros()
    S = sep(omega, P)
    # Check the three hypotheses of `eq_omega_of_inductive` for S.
    l.have(S <= omega, by=[le.defn(S, omega), zf.elem_sep])
    l.have(elem(zero, S), by=[zf.elem_sep(P, omega, zero), omega_zero])
    l.have(ForAll(n, elem(n, S), elem(succ(n), S)), by=[zf.elem_sep, omega_succ])
    l.have(S == omega, by=[eq_omega_of_inductive(S)])
    k = l.fix()
    l.auto(by=[zf.elem_sep(P, omega, k)])


# Induction at one point, in the shape `l.induct` applies.
omega_induction_at = prove(
    ForAll(
        [P, x],
        Implies(And(P[zero], ForAll(n, elem(n, omega), P[n], P[succ(n)]), elem(x, omega)), P[x]),
    ),
    by=[omega_induction],
)


def induct_omega(x: kd.smt.ExprRef, P: kd.smt.QuantifierRef) -> kd.Proof:
    """`using=` hook: `l.induct(n, using=induct_omega)` leaves goals P(0), the step, and n ∈ ω."""
    # Instantiate, then beta-reduce. Proving the reduced statement directly
    # from `omega_induction(P)` made z3 match P[k] under binders, which was
    # seed- and state-dependent.
    inst = omega_induction_at(P, x)
    thm = kd.rewrite.beta(inst.thm)
    assert isinstance(thm, kd.smt.BoolRef)
    return kd.prove(thm, by=[inst])


# Transitivity and the Peano axiom V (Halmos §12)

is_transitive = define("is_transitive", [A], ForAll(x, elem(x, A), x <= A))


# z ∈ A gives z ⊆ A ⊆ succ A; z = A gives z ⊆ succ A directly.
is_transitive_succ = prove(
    ForAll(A, is_transitive(A), is_transitive(succ(A))),
    by=[is_transitive.defn, elem_succ, le_succ, le.defn],
)


@Theorem(ForAll(n, elem(n, omega), is_transitive(n)))
def nat_is_transitive(l):
    """Halmos §12 (ii): every element of a natural number is a subset of it."""
    n = l.fix()
    l.intro()
    l.induct(n, using=induct_omega)
    l.auto(by=[is_transitive.defn(zero), zero.defn, zf.elem_emp])
    k = l.fix()
    l.auto(by=[is_transitive_succ(k)])


@Theorem(ForAll(n, elem(n, omega), ForAll(x, elem(x, n), Not(n <= x))))
def nat_not_le_of_elem(l):
    """Halmos §12 (i): no natural number is a subset of one of its elements."""
    n = l.fix()
    l.intro()
    l.induct(n, using=induct_omega)
    l.auto(by=[zero.defn, zf.elem_emp])
    k = l.fix()
    l.intros()
    x = l.fix()
    l.intro()
    l.intro()
    # Since k ⊆ k, k ∉ k.
    l.have(Not(elem(k, k)), by=[le.defn(k, k)])
    # If k⁺ ⊆ x, then k ⊆ x and k ∈ x.
    l.have(k <= x, by=[le_succ(k), le.defn])
    l.have(elem(k, x), by=[elem_succ_self(k), le.defn])
    # So x ≠ k, as k ∉ k; and x ∉ k, as k ⊆ x. Neither is possible for x ∈ k⁺.
    l.auto(by=[elem_succ(x, k)])


nat_not_elem_self = prove(
    ForAll(n, elem(n, omega), Not(elem(n, n))), by=[nat_not_le_of_elem, le.defn]
)
succ_ne_self = prove(
    ForAll(n, elem(n, omega), succ(n) != n), by=[nat_not_elem_self, elem_succ_self]
)


@Theorem(ForAll([n, m], elem(n, omega), elem(m, omega), (succ(n) == succ(m)) == (n == m)))
def succ_inj(l):
    """Peano V"""
    n, m = l.fixes()
    l.intros()
    l.split()
    l.intro()
    # n ∈ succ m and m ∈ succ n, so either n = m or n ∈ m ∈ n.
    l.have(Or(elem(n, m), n == m), by=[elem_succ(n, m), elem_succ_self(n)])
    l.have(Or(elem(m, n), m == n), by=[elem_succ(m, n), elem_succ_self(m)])
    # n ∈ m ∈ n with n transitive would put n ∈ n.
    l.auto(by=[nat_is_transitive(n), is_transitive.defn(n), le.defn, nat_not_elem_self(n)])
    l.auto()


@Theorem(ForAll(n, elem(n, omega), n != zero, Exists(m, And(elem(m, omega), n == succ(m)))))
def exists_eq_succ_of_ne_zero(l):
    n = l.fix()
    l.intro()
    l.induct(n, using=induct_omega)
    l.auto()
    # succ k is the successor of k.
    k = l.fix()
    l.intros()
    l.exists(k)
    l.auto()


@Theorem(is_transitive(omega))
def omega_is_transitive(l):
    l.unfold(is_transitive)
    n = l.fix()
    l.intro()
    l.induct(n, using=induct_omega)
    l.auto(by=[le.defn, zero.defn, zf.elem_emp])
    # If k ⊆ ω and k ∈ ω then succ k = k ∪ {k} ⊆ ω.
    l.fix()
    l.auto(by=[elem_succ, le.defn])


# Small naturals.

one = succ(zero)
zero_ne_one = prove(Not(zero == one), by=[succ_ne_zero])
elem_one = prove(ForAll(x, elem(x, one) == (x == zero)), by=[elem_succ, zero.defn, zf.elem_emp])
two = succ(one)
elem_two = prove(ForAll(x, elem(x, two) == Or(x == zero, x == one)), by=[elem_succ, elem_one])
