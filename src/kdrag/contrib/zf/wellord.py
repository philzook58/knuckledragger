"""
The well ordering theorem (Halmos §17).

Halmos derives it from Zorn's lemma, applied to the well ordered subsets of X.
Here it falls out of the towers from `zorn` more directly. Take K = P(X), so
that g(A) adds one chosen point of X − A to A, and order X by when points enter
the smallest tower T₀:

    x ≼ y  iff  every A ∈ T₀ that contains y contains x.

For a nonempty E ⊆ X, let A be the union of the members of T₀ that miss E.
Then A is in T₀ and misses E, while g(A) meets E, and the point it adds is the
least element of E.
"""

from kdrag import Theorem, define
from kdrag.smt import And, Eq, ArraySort, BoolSort, Consts, Exists, ForAll, Lambda, Not
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import ZFSet, bigunion, elem, le, pow, upair
from kdrag.contrib.zf.choice import exists_choice_on, is_choice_on
from kdrag.contrib.zf.poset import is_least, is_partial_order, is_well_order
from kdrag.contrib.zf.zorn import (
    comparable_t0,
    eq_of_nxt_eq,
    is_chain,
    is_tower,
    is_tukey,
    le_nxt,
    nxt,
    nxt_le_of_ssubset,
    nxt_sub_subsingleton,
    tower0,
    tower0_chain,
    tower0_tower,
)
from kdrag.contrib.zf._sep import define_sep

A, B, C, E, X, f, x, y = Consts("A B C E X f x y", ZFSet)
R = Consts("R", ArraySort(ZFSet, ZFSet, BoolSort()))[0]
emp = zf.emp


@Theorem(ForAll(X, is_tukey(pow(X), X)))
def pow_tukey(l):
    """P(X) satisfies Halmos' hypotheses on K."""
    X = l.fix()
    l.unfold(is_tukey)
    l.split()
    l.auto(by=[le.defn])
    l.have(elem(emp, pow(X)), by=[zf.elem_pow(X, emp), le.defn, zf.elem_emp])
    l.auto(by=[zf.elem_emp(emp)])
    l.auto(by=[zf.elem_pow, le.defn])
    l.fix()
    l.intros()
    l.auto(by=[zf.elem_pow, le.defn, zf.bigunion_ax])


def _hyps(f, X):
    return [is_choice_on(f, X)]


@Theorem(
    ForAll(
        [f, X, A],
        is_choice_on(f, X),
        elem(A, pow(X)),
        nxt(f, pow(X), X, A) == A,
        A == X,
    )
)
def eq_of_nxt_eq_pow(l):
    """In P(X), g(A) = A only for A = X."""
    f, X, A = l.fixes()
    l.intros()
    l.have(elem(X, pow(X)), by=[zf.elem_pow(X, X), le.defn])
    l.have(A <= X, by=[zf.elem_pow(X, A)])
    l.auto(by=[eq_of_nxt_eq(f, pow(X), X, A, X), pow_tukey(X)])


@Theorem(
    ForAll(
        [f, X, A],
        is_choice_on(f, X),
        elem(A, tower0(f, pow(X), X)),
        comparable_t0(f, pow(X), X, A),
    )
)
def comparable_of_elem_tower0(l):
    """Every member of T₀ is comparable, as T₀ is a chain."""
    f, X, A = l.fixes()
    l.intros()
    l.have(is_chain(tower0(f, pow(X), X)), by=[tower0_chain(f, pow(X), X), pow_tukey])
    l.unfold(comparable_t0)
    l.auto(by=[is_chain.defn])


# The members of T₀ that miss E.
missing, elem_missing = define_sep(
    "missing",
    [f, X, E],
    tower0(f, pow(X), X),
    A,
    ForAll(x, elem(x, E), Not(elem(x, A))),
)


@Theorem(
    ForAll(
        [f, X, E],
        is_choice_on(f, X),
        E <= X,
        E != emp,
        Exists(
            A,
            And(
                elem(A, tower0(f, pow(X), X)),
                ForAll(x, elem(x, E), Not(elem(x, A))),
                Exists(x, And(elem(x, E), elem(x, nxt(f, pow(X), X, A)))),
            ),
        ),
    )
)
def exists_first(l):
    """The union A of the members of T₀ that miss E is in T₀ and misses E. If
    g(A) missed E too, then g(A) ⊆ A, so A = X, which meets E."""
    f, X, E = l.fixes()
    l.intros()
    P = pow(X)
    T0 = tower0(f, P, X)
    M = missing(f, X, E)
    A0 = bigunion(M)
    l.have(is_tower(T0, f, P, X), by=[tower0_tower(f, P, X), pow_tukey])
    l.have(is_chain(T0), by=[tower0_chain(f, P, X), pow_tukey])
    l.have(M <= T0, by=[le.defn, elem_missing])
    l.have(is_chain(M), by=[is_chain.defn, le.defn(M, T0)])
    l.have(elem(A0, T0), by=[is_tower.defn(T0, f, P, X)])
    l.have(ForAll(x, elem(x, E), Not(elem(x, A0))), by=[zf.bigunion_ax, elem_missing])
    l.exists(A0)
    gA = nxt(f, P, X, A0)
    l.have(elem(gA, T0), by=[is_tower.defn(T0, f, P, X)])
    l.cases(
        ForAll(x, elem(x, E), Not(elem(x, gA))), Exists(x, And(elem(x, E), elem(x, gA)))
    )
    # Then g(A) ∈ M, so g(A) ⊆ A and A = X.
    l.have(elem(gA, M), by=[elem_missing(f, X, E, gA)])
    l.have(gA <= A0, by=[le.defn, zf.bigunion_ax])
    l.have(gA == A0, by=[le_nxt(f, P, X, A0), zf.ext_ax, le.defn])
    l.have(elem(A0, P), by=[is_tower.defn(T0, f, P, X), le.defn(T0, P)])
    l.have(A0 == X, by=[eq_of_nxt_eq_pow(f, X, A0)])
    l.have(Exists(x, elem(x, E)), by=[zf.not_emp_exists_elem(E)])
    x0, _ = l.obtain(-1)
    l.auto(by=[le.defn(E, X)])
    l.auto()


# x ≼ y: x enters T₀ no later than y.
wo_rel = define(
    "wo_rel",
    [f, X],
    Lambda([x, y], ForAll(A, elem(A, tower0(f, pow(X), X)), elem(y, A), elem(x, A))),
)


@Theorem(
    ForAll(
        [f, X, x, y],
        Eq(
            wo_rel(f, X)[x, y],
            ForAll(A, elem(A, tower0(f, pow(X), X)), elem(y, A), elem(x, A)),
        ),
    )
)
def wo_rel_apply(l):
    l.fixes()
    l.unfold(wo_rel)
    l.simp()
    l.auto()


@Theorem(
    ForAll(
        [f, X, E],
        is_choice_on(f, X),
        E <= X,
        E != emp,
        Exists(x, is_least(wo_rel(f, X), E, x)),
    )
)
def exists_least_wo_rel(l):
    """The point x of E added by g(A) is least: a member B of T₀ containing
    y ∈ E does not lie inside A, so A ⊊ B and g(A) ⊆ B."""
    f, X, E = l.fixes()
    l.intros()
    P = pow(X)
    T0 = tower0(f, P, X)
    l.have(
        Exists(
            A,
            And(
                elem(A, T0),
                ForAll(x, elem(x, E), Not(elem(x, A))),
                Exists(x, And(elem(x, E), elem(x, nxt(f, P, X, A)))),
            ),
        ),
        by=[exists_first(f, X, E)],
    )
    A0, _ = l.obtain(-1)
    l.have(Exists(x, And(elem(x, E), elem(x, nxt(f, P, X, A0)))))
    l.auto()
    x0, _ = l.obtain(-1)
    l.exists(x0)
    l.unfold(is_least)
    l.split()
    l.auto()
    l.fix()
    l.intro()
    l.rw(wo_rel_apply)
    B0 = l.fix()
    l.intros()
    l.have(comparable_t0(f, P, X, B0), by=[comparable_of_elem_tower0(f, X, B0)])
    l.have(A0 <= B0, by=[comparable_t0.defn(f, P, X, B0), le.defn(B0, A0)])
    l.have(A0 != B0)
    l.auto()
    l.have(
        nxt(f, P, X, A0) <= B0, by=[nxt_le_of_ssubset(f, P, X, B0, A0), pow_tukey(X)]
    )
    l.auto(by=[le.defn(nxt(f, P, X, A0), B0)])


@Theorem(ForAll([f, X], is_choice_on(f, X), is_well_order(wo_rel(f, X), X)))
def wo_rel_well_order(l):
    """≼ is a well ordering of X. Reflexivity and transitivity are immediate. If
    x ≼ y ≼ x, the first tower step that adds x or y adds both, so x = y."""
    f, X = l.fixes()
    l.intro()
    P = pow(X)
    T0 = tower0(f, P, X)
    l.unfold(is_well_order)
    l.split()
    l.unfold(is_partial_order)
    l.split()
    l.auto(by=[wo_rel_apply])
    x0, y0 = l.fixes()
    l.intros()
    E0 = upair(x0, y0)
    l.have(E0 <= X, by=[le.defn, zf.elem_upair])
    l.have(E0 != emp, by=[zf.upair_not_emp])
    l.have(
        Exists(
            A,
            And(
                elem(A, T0),
                ForAll(x, elem(x, E0), Not(elem(x, A))),
                Exists(x, And(elem(x, E0), elem(x, nxt(f, P, X, A)))),
            ),
        ),
        by=[exists_first(f, X, E0)],
    )
    A0, _ = l.obtain(-1)
    gA = nxt(f, P, X, A0)
    l.have(elem(gA, T0), by=[tower0_tower(f, P, X), pow_tukey, is_tower.defn])
    # Both points are new in g(A).
    l.have(
        And(elem(x0, gA), elem(y0, gA)),
        by=[wo_rel_apply(f, X, x0, y0), wo_rel_apply(f, X, y0, x0), zf.elem_upair],
    )
    l.auto(by=[nxt_sub_subsingleton(f, P, X, A0, x0, y0), zf.elem_upair])
    l.auto(by=[wo_rel_apply])
    l.auto(by=[exists_least_wo_rel])


@Theorem(ForAll(X, Exists(R, is_well_order(R, X))))
def exists_well_order(l):
    """Halmos §17, the well ordering theorem: every set can be well ordered."""
    X = l.fix()
    l.have(Exists(f, is_choice_on(f, X)), by=[exists_choice_on(X)])
    f0, _ = l.obtain(-1)
    l.exists(wo_rel(f0, X))
    l.auto(by=[wo_rel_well_order(f0, X)])
