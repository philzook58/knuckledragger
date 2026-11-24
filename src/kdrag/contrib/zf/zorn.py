"""
Zorn's lemma (Halmos §16).

Halmos first proves it for a collection K of subsets of X, ordered by
inclusion, that contains ∅, is closed under subsets, and contains the union of
each of its chains. With a choice function f, the step

    g(A) = A ∪ {f(Â − A)},  where Â = {x ∈ X | A ∪ {x} ∈ K},

adds one new point when it can and is the identity exactly at maximal A. A
tower is a subcollection that contains ∅ and is closed under g and under unions
of chains. The smallest tower T₀ is a chain, so its union A is in T₀, and
then g(A) ⊆ A says that A is maximal. Zorn's lemma for a partial order follows
by applying this to the collection of its chains.
"""

from kdrag import Theorem, define
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
)
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import ZFSet, bigunion, elem, le, pow, sep, sing
from kdrag.contrib.zf.choice import exists_choice_on, is_choice_on
from kdrag.contrib.zf.fun import app, elem_sub
from kdrag.contrib.zf.poset import (
    is_partial_order,
    partial_order_antisymm,
    partial_order_refl,
    partial_order_trans,
)

A, B, C, K, T, X, f, x, y = Consts("A B C K T X f x y", ZFSet)

emp = zf.emp

# C is a chain under inclusion.
is_chain = define(
    "is_chain", [C], ForAll([A, B], elem(A, C), elem(B, C), Or(A <= B, B <= A))
)

# Halmos' hypotheses on K: subsets of X, nonempty, closed under subsets, and
# containing the union of each chain.
is_tukey = define(
    "is_tukey",
    [K, X],
    And(
        K <= pow(X),
        K != emp,
        ForAll([A, B], elem(A, K), B <= A, elem(B, K)),
        ForAll(C, C <= K, is_chain(C), elem(bigunion(C), K)),
    ),
)

# Â: the points that can be added to A without leaving K.
hat = define("hat", [K, X, A], sep(X, Lambda(x, elem(A | sing(x), K))))


@Theorem(
    ForAll([K, X, A, x], elem(x, hat(K, X, A)) == And(elem(x, X), elem(A | sing(x), K)))
)
def elem_hat(l):
    l.fixes()
    l.unfold(hat)
    l.rw(zf.elem_sep)
    l.simp()
    l.auto()


# Halmos' g: add the chosen new point of Â, if there is one.
nxt = define(
    "nxt",
    [f, K, X, A],
    If(
        hat(K, X, A) - A == emp,
        A,
        A | sing(app(f, hat(K, X, A) - A)),
    ),
)


def _hyps(f, K, X):
    return [is_choice_on(f, X), is_tukey(K, X)]


@Theorem(ForAll([f, K, X, A], A <= nxt(f, K, X, A)))
def le_nxt(l):
    f, K, X, A = l.fixes()
    l.unfold(nxt)
    l.auto(by=[le.defn, zf.elem_union])


@Theorem(
    ForAll(
        [f, K, X, A, x, y],
        elem(x, nxt(f, K, X, A)),
        Not(elem(x, A)),
        elem(y, nxt(f, K, X, A)),
        Not(elem(y, A)),
        x == y,
    )
)
def nxt_sub_subsingleton(l):
    """g(A) − A has at most one element."""
    f, K, X, A, x0, y0 = l.fixes()
    l.intros()
    l.unfold(nxt, at=0)
    l.unfold(nxt, at=2)
    l.auto(by=[zf.elem_union, zf.elem_sing])


@Theorem(ForAll([f, K, X, A], *_hyps(f, K, X), elem(A, K), elem(nxt(f, K, X, A), K)))
def nxt_elem(l):
    """g(A) stays in K: the chosen point x lies in Â, so A ∪ {x} ∈ K."""
    f, K, X, A = l.fixes()
    l.intros()
    D = hat(K, X, A) - A
    l.unfold(nxt)
    l.cases(D == emp, D != emp)
    l.auto()
    l.have(D <= X, by=[le.defn, elem_sub, elem_hat])
    l.have(elem(app(f, D), D), by=[is_choice_on.defn(f, X)])
    l.auto(by=[elem_sub(app(f, D), hat(K, X, A), A), elem_hat(K, X, A, app(f, D))])


@Theorem(
    ForAll(
        [f, K, X, A, B],
        *_hyps(f, K, X),
        elem(A, K),
        nxt(f, K, X, A) == A,
        elem(B, K),
        A <= B,
        B == A,
    )
)
def eq_of_nxt_eq(l):
    """If g(A) = A then A is maximal: a point of B − A could be added to A."""
    f, K, X, A, B = l.fixes()
    l.intros()
    D = hat(K, X, A) - A
    l.rw(zf.ext_ax)
    x0 = l.fix()
    l.split()
    l.intro()
    l.contra()
    # A ∪ {x} ⊆ B is in K, so x ∈ Â − A, and then g(A) ≠ A.
    l.have(A | sing(x0) <= B, by=[le.defn, zf.elem_union, zf.elem_sing])
    l.have(
        elem(A | sing(x0), K),
        by=[is_tukey.defn(K, X)],
    )
    l.have(elem(B, pow(X)), by=[is_tukey.defn(K, X), le.defn(K, pow(X))])
    l.have(elem(x0, X), by=[zf.elem_pow(X, B), le.defn(B, X)])
    l.have(elem(x0, D), by=[elem_sub(x0, hat(K, X, A), A), elem_hat(K, X, A, x0)])
    l.have(D != emp, by=[zf.elem_emp(x0)])
    l.have(D <= X, by=[le.defn, elem_sub, elem_hat])
    l.have(elem(app(f, D), D), by=[is_choice_on.defn(f, X)])
    l.have(
        elem(app(f, D), nxt(f, K, X, A)),
        by=[nxt.defn(f, K, X, A), zf.elem_union, zf.elem_sing],
    )
    l.auto(by=[elem_sub(app(f, D), hat(K, X, A), A)])
    l.intro()
    l.auto(by=[le.defn(A, B)])


# Halmos' towers: subcollections of K with ∅, closed under g and unions of chains.
is_tower = define(
    "is_tower",
    [T, f, K, X],
    And(
        T <= K,
        elem(emp, T),
        ForAll(A, elem(A, T), elem(nxt(f, K, X, A), T)),
        ForAll(C, C <= T, is_chain(C), elem(bigunion(C), T)),
    ),
)


@Theorem(ForAll([f, K, X], *_hyps(f, K, X), is_tower(K, f, K, X)))
def tower_self(l):
    """K itself is a tower, so towers exist."""
    f, K, X = l.fixes()
    l.intros()
    l.have(Exists(A, elem(A, K)), by=[is_tukey.defn(K, X), zf.not_emp_exists_elem(K)])
    A0, _ = l.obtain(-1)
    l.have(emp <= A0, by=[le.defn, zf.elem_emp])
    l.unfold(is_tower)
    l.auto(by=[is_tukey.defn(K, X), le.defn(K, K), nxt_elem])


# T₀, the intersection of all towers.
tower0 = define(
    "tower0", [f, K, X], sep(K, Lambda(A, ForAll(T, is_tower(T, f, K, X), elem(A, T))))
)


@Theorem(
    ForAll(
        [f, K, X, A],
        elem(A, tower0(f, K, X))
        == And(elem(A, K), ForAll(T, is_tower(T, f, K, X), elem(A, T))),
    )
)
def elem_tower0(l):
    l.fixes()
    l.unfold(tower0)
    l.rw(zf.elem_sep)
    l.simp()
    l.auto()


@Theorem(ForAll([f, K, X, T], is_tower(T, f, K, X), tower0(f, K, X) <= T))
def tower0_le(l):
    f, K, X, T = l.fixes()
    l.intro()
    l.rw(le.defn)
    A0 = l.fix()
    l.intro()
    l.auto(by=[elem_tower0(f, K, X, A0)])


@Theorem(ForAll([f, K, X], *_hyps(f, K, X), is_tower(tower0(f, K, X), f, K, X)))
def tower0_tower(l):
    """T₀ is a tower: each closure property holds in every tower."""
    f, K, X = l.fixes()
    l.intros()
    l.have(is_tower(K, f, K, X), by=[tower_self(f, K, X)])
    l.unfold(is_tower)
    l.split()
    l.auto(by=[le.defn, elem_tower0])
    l.auto(by=[elem_tower0(f, K, X, emp), is_tower.defn])
    A0 = l.fix()
    l.intro()
    l.auto(
        by=[
            elem_tower0(f, K, X, A0),
            elem_tower0(f, K, X, nxt(f, K, X, A0)),
            is_tower.defn,
        ]
    )
    C0 = l.fix()
    l.intros()
    l.have(ForAll(T, is_tower(T, f, K, X), C0 <= T), by=[le.defn, elem_tower0])
    l.auto(by=[elem_tower0(f, K, X, bigunion(C0)), is_tower.defn])


@Theorem(
    ForAll(
        [f, K, X, T],
        is_tower(T, f, K, X),
        T <= tower0(f, K, X),
        T == tower0(f, K, X),
    )
)
def eq_tower0(l):
    """A tower inside T₀ is T₀."""
    f, K, X, T = l.fixes()
    l.intros()
    l.auto(by=[tower0_le(f, K, X, T), zf.ext_ax, le.defn])


# C is comparable: every member of T₀ is inside it or contains it.
comparable_t0 = define(
    "comparable_t0",
    [f, K, X, C],
    ForAll(A, elem(A, tower0(f, K, X)), Or(A <= C, C <= A)),
)


@Theorem(
    ForAll(
        [f, K, X, C, A],
        *_hyps(f, K, X),
        comparable_t0(f, K, X, C),
        elem(A, tower0(f, K, X)),
        A <= C,
        A != C,
        nxt(f, K, X, A) <= C,
    )
)
def nxt_le_of_ssubset(l):
    """Halmos: if A ⊊ C with C comparable, then g(A) ⊆ C. Otherwise C ⊊ g(A),
    and g(A) − A would have two elements, one in C and one outside it."""
    f, K, X, C, A = l.fixes()
    l.intros()
    gA = nxt(f, K, X, A)
    T0 = tower0(f, K, X)
    l.have(elem(gA, T0), by=[tower0_tower(f, K, X), is_tower.defn(T0, f, K, X)])
    l.have(Or(gA <= C, C <= gA), by=[comparable_t0.defn(f, K, X, C)])
    l.contra()
    # x ∈ g(A) − C and y ∈ C − A are both new points of g(A).
    l.have(Exists(x, And(elem(x, gA), Not(elem(x, C)))), by=[le.defn(gA, C)])
    x0, _ = l.obtain(-1)
    l.have(
        Exists(y, And(elem(y, C), Not(elem(y, A)))), by=[zf.ext_ax(A, C), le.defn(A, C)]
    )
    y0, _ = l.obtain(-1)
    l.auto(
        by=[
            le.defn(A, C),
            le.defn(C, gA),
            nxt_sub_subsingleton(f, K, X, A, x0, y0),
        ]
    )


# Halmos' U(C): the members of T₀ inside C or containing g(C).
ubar = define(
    "ubar",
    [f, K, X, C],
    sep(tower0(f, K, X), Lambda(A, Or(A <= C, nxt(f, K, X, C) <= A))),
)


@Theorem(
    ForAll(
        [f, K, X, C, A],
        elem(A, ubar(f, K, X, C))
        == And(elem(A, tower0(f, K, X)), Or(A <= C, nxt(f, K, X, C) <= A)),
    )
)
def elem_ubar(l):
    l.fixes()
    l.unfold(ubar)
    l.rw(zf.elem_sep)
    l.simp()
    l.auto()


@Theorem(
    ForAll(
        [f, K, X, C],
        *_hyps(f, K, X),
        elem(C, tower0(f, K, X)),
        comparable_t0(f, K, X, C),
        is_tower(ubar(f, K, X, C), f, K, X),
    )
)
def ubar_tower(l):
    """Halmos: U(C) is a tower, for comparable C."""
    f, K, X, C = l.fixes()
    l.intros()
    T0 = tower0(f, K, X)
    U = ubar(f, K, X, C)
    gC = nxt(f, K, X, C)
    l.have(is_tower(T0, f, K, X), by=[tower0_tower(f, K, X)])
    l.unfold(is_tower)
    l.split()
    l.auto(by=[le.defn, elem_ubar, is_tower.defn(T0, f, K, X)])
    l.auto(
        by=[
            elem_ubar(f, K, X, C, emp),
            is_tower.defn(T0, f, K, X),
            le.defn,
            zf.elem_emp,
        ]
    )
    # A ∈ U gives g(A) ∈ U: A ⊊ C, A = C, or g(C) ⊆ A ⊆ g(A).
    A0 = l.fix()
    l.intro()
    gA = nxt(f, K, X, A0)
    l.have(
        And(elem(A0, T0), Or(A0 <= C, gC <= A0)),
        by=[elem_ubar(f, K, X, C, A0)],
    )
    l.have(elem(gA, T0), by=[is_tower.defn(T0, f, K, X)])
    l.have(A0 <= gA, by=[le_nxt(f, K, X, A0)])
    l.have(Or(gA <= C, gC <= gA))
    l.cases(And(A0 <= C, A0 != C), A0 == C, gC <= A0)
    l.auto(by=[nxt_le_of_ssubset(f, K, X, C, A0)])
    l.auto(by=[le.defn(gC, gC)])
    l.auto(by=[le.defn(gC, A0), le.defn(A0, gA), le.defn(gC, gA)])
    l.auto(by=[elem_ubar(f, K, X, C, gA)])
    # A chain in U: either all of it lies in C, or some member contains g(C).
    C1 = l.fix()
    l.intros()
    l.have(C1 <= T0, by=[le.defn(C1, U), le.defn(C1, T0), elem_ubar])
    l.have(elem(bigunion(C1), T0), by=[is_tower.defn(T0, f, K, X)])
    l.cases(
        ForAll(A, elem(A, C1), A <= C),
        Exists(A, And(elem(A, C1), Not(A <= C))),
    )
    l.have(bigunion(C1) <= C, by=[le.defn, zf.bigunion_ax])
    l.auto(by=[elem_ubar(f, K, X, C, bigunion(C1))])
    A1, _ = l.obtain(-1)
    l.have(gC <= A1, by=[le.defn(C1, U), elem_ubar(f, K, X, C, A1)])
    l.have(A1 <= bigunion(C1), by=[le.defn, zf.bigunion_ax])
    l.auto(
        by=[
            elem_ubar(f, K, X, C, bigunion(C1)),
            le.defn(gC, A1),
            le.defn(A1, bigunion(C1)),
            le.defn(gC, bigunion(C1)),
        ]
    )


@Theorem(
    ForAll(
        [f, K, X, C],
        *_hyps(f, K, X),
        elem(C, tower0(f, K, X)),
        comparable_t0(f, K, X, C),
        comparable_t0(f, K, X, nxt(f, K, X, C)),
    )
)
def comparable_nxt(l):
    """Halmos: U(C) = T₀, so each A ∈ T₀ has A ⊆ C ⊆ g(C) or g(C) ⊆ A."""
    f, K, X, C = l.fixes()
    l.intros()
    T0 = tower0(f, K, X)
    U = ubar(f, K, X, C)
    gC = nxt(f, K, X, C)
    l.have(U <= T0, by=[le.defn, elem_ubar])
    l.have(U == T0, by=[eq_tower0(f, K, X, U), ubar_tower(f, K, X, C)])
    l.have(C <= gC, by=[le_nxt(f, K, X, C)])
    l.unfold(comparable_t0)
    A0 = l.fix()
    l.intro()
    l.auto(
        by=[elem_ubar(f, K, X, C, A0), le.defn(A0, C), le.defn(C, gC), le.defn(A0, gC)]
    )


comparables = define(
    "comparables",
    [f, K, X],
    sep(tower0(f, K, X), Lambda(C, comparable_t0(f, K, X, C))),
)


@Theorem(
    ForAll(
        [f, K, X, C],
        elem(C, comparables(f, K, X))
        == And(elem(C, tower0(f, K, X)), comparable_t0(f, K, X, C)),
    )
)
def elem_comparables(l):
    l.fixes()
    l.unfold(comparables)
    l.rw(zf.elem_sep)
    l.simp()
    l.auto()


@Theorem(ForAll([f, K, X], *_hyps(f, K, X), is_chain(tower0(f, K, X))))
def tower0_chain(l):
    """Halmos: the comparable sets form a tower, so all of T₀ is comparable,
    which says T₀ is a chain."""
    f, K, X = l.fixes()
    l.intros()
    T0 = tower0(f, K, X)
    Cm = comparables(f, K, X)
    l.have(is_tower(T0, f, K, X), by=[tower0_tower(f, K, X)])
    l.have(is_tower(Cm, f, K, X))
    l.unfold(is_tower)
    l.split()
    l.auto(by=[le.defn, elem_comparables, is_tower.defn(T0, f, K, X)])
    l.auto(
        by=[
            elem_comparables(f, K, X, emp),
            comparable_t0.defn(f, K, X, emp),
            is_tower.defn(T0, f, K, X),
            le.defn,
            zf.elem_emp,
        ]
    )
    C0 = l.fix()
    l.intro()
    l.auto(
        by=[
            elem_comparables(f, K, X, C0),
            elem_comparables(f, K, X, nxt(f, K, X, C0)),
            comparable_nxt(f, K, X, C0),
            is_tower.defn(T0, f, K, X),
        ]
    )
    # A union of comparable sets is comparable: A ⊆ every member, or some member
    # escapes A and then contains it.
    C1 = l.fix()
    l.intros()
    V = bigunion(C1)
    l.have(C1 <= T0, by=[le.defn(C1, Cm), le.defn(C1, T0), elem_comparables])
    l.have(elem(V, T0), by=[is_tower.defn(T0, f, K, X)])
    l.have(comparable_t0(f, K, X, V))
    l.unfold(comparable_t0)
    A0 = l.fix()
    l.intro()
    l.cases(
        ForAll(B, elem(B, C1), B <= A0),
        Exists(B, And(elem(B, C1), Not(B <= A0))),
    )
    l.auto(by=[le.defn, zf.bigunion_ax])
    B0, _ = l.obtain(-1)
    l.have(
        comparable_t0(f, K, X, B0),
        by=[le.defn(C1, Cm), elem_comparables(f, K, X, B0)],
    )
    l.have(A0 <= B0, by=[comparable_t0.defn(f, K, X, B0)])
    l.have(B0 <= V, by=[le.defn, zf.bigunion_ax])
    l.auto(by=[le.defn(A0, B0), le.defn(B0, V), le.defn(A0, V)])
    l.auto(by=[elem_comparables(f, K, X, V)])
    l.have(Cm <= T0, by=[le.defn, elem_comparables])
    l.have(Cm == T0, by=[eq_tower0(f, K, X, Cm)])
    l.unfold(is_chain)
    A1, B1 = l.fixes()
    l.intros()
    l.auto(by=[elem_comparables(f, K, X, B1), comparable_t0.defn(f, K, X, B1)])


@Theorem(
    ForAll(
        [K, X],
        is_tukey(K, X),
        Exists(A, And(elem(A, K), ForAll(B, elem(B, K), A <= B, B == A))),
    )
)
def exists_maximal_of_tukey(l):
    """Halmos §16: a nonempty collection of subsets of X that is closed under
    subsets and under unions of chains has a maximal member: the union A of T₀,
    for which g(A) ⊆ A."""
    K, X = l.fixes()
    l.intro()
    l.have(Exists(f, is_choice_on(f, X)), by=[exists_choice_on(X)])
    f0, _ = l.obtain(-1)
    T0 = tower0(f0, K, X)
    A0 = bigunion(T0)
    l.have(is_tower(T0, f0, K, X), by=[tower0_tower(f0, K, X)])
    l.have(is_chain(T0), by=[tower0_chain(f0, K, X)])
    l.have(elem(A0, T0), by=[is_tower.defn(T0, f0, K, X), le.defn(T0, T0)])
    gA = nxt(f0, K, X, A0)
    l.have(elem(gA, T0), by=[is_tower.defn(T0, f0, K, X)])
    l.have(gA <= A0, by=[le.defn, zf.bigunion_ax])
    l.have(gA == A0, by=[le_nxt(f0, K, X, A0), zf.ext_ax, le.defn])
    l.have(elem(A0, K), by=[is_tower.defn(T0, f0, K, X), le.defn(T0, K)])
    l.exists(A0)
    l.auto(by=[eq_of_nxt_eq])


# Zorn's lemma for a partial order R on X.

R = Consts("R", ArraySort(ZFSet, ZFSet, BoolSort()))[0]
E, m, u = Consts("E m u", ZFSet)

# E is a chain of R: any two of its elements are comparable.
is_chain_of = define(
    "is_chain_of",
    [R, E],
    ForAll([x, y], elem(x, E), elem(y, E), Or(R[x, y], R[y, x])),
)
chains = define("chains", [R, X], sep(pow(X), Lambda(E, is_chain_of(R, E))))


@Theorem(
    ForAll(
        [R, X, E],
        elem(E, chains(R, X)) == And(E <= X, is_chain_of(R, E)),
    )
)
def elem_chains(l):
    l.fixes()
    l.unfold(chains)
    l.rw(zf.elem_sep)
    l.simp()
    l.auto(by=[zf.elem_pow])


@Theorem(ForAll([R, X], is_tukey(chains(R, X), X)))
def chains_tukey(l):
    """The chains of X satisfy Halmos' hypotheses: ∅ is a chain, so is every part
    of a chain, and so is the union of a chain of chains."""
    R, X = l.fixes()
    Ch = chains(R, X)
    l.unfold(is_tukey)
    l.split()
    l.auto(by=[le.defn, elem_chains, zf.elem_pow])
    l.have(
        elem(emp, Ch),
        by=[elem_chains(R, X, emp), le.defn, zf.elem_emp, is_chain_of.defn],
    )
    l.auto(by=[zf.elem_emp(emp)])
    A0, B0 = l.fixes()
    l.intros()
    l.auto(
        by=[
            elem_chains(R, X, A0),
            elem_chains(R, X, B0),
            is_chain_of.defn(R, A0),
            is_chain_of.defn(R, B0),
            le.defn,
        ]
    )
    # x ∈ A₁, y ∈ A₂ with A₁ ⊆ A₂ say, so both lie in the chain A₂.
    C0 = l.fix()
    l.intros()
    V = bigunion(C0)
    l.have(V <= X, by=[le.defn, zf.bigunion_ax, le.defn(C0, Ch), elem_chains])
    l.have(is_chain_of(R, V))
    l.unfold(is_chain_of)
    x0, y0 = l.fixes()
    l.intros()
    l.have(Exists(A, And(elem(A, C0), elem(x0, A))), by=[zf.bigunion_ax(C0, x0)])
    A1, _ = l.obtain(-1)
    l.have(Exists(A, And(elem(A, C0), elem(y0, A))), by=[zf.bigunion_ax(C0, y0)])
    A2, _ = l.obtain(-1)
    l.auto(
        by=[
            is_chain.defn(C0),
            le.defn(A1, A2),
            le.defn(A2, A1),
            le.defn(C0, Ch),
            elem_chains(R, X, A1),
            elem_chains(R, X, A2),
            is_chain_of.defn(R, A1),
            is_chain_of.defn(R, A2),
        ]
    )
    l.auto(by=[elem_chains(R, X, V)])


@Theorem(
    ForAll(
        [R, X],
        is_partial_order(R, X),
        ForAll(
            E,
            E <= X,
            is_chain_of(R, E),
            Exists(u, And(elem(u, X), ForAll(x, elem(x, E), R[x, u]))),
        ),
        Exists(m, And(elem(m, X), ForAll(x, elem(x, X), R[m, x], x == m))),
    )
)
def zorn(l):
    """Halmos §16, Zorn's lemma: if every chain in a partially ordered set X has
    an upper bound, then X has a maximal element. An upper bound u of a maximal
    chain M is one: if u ≤ x, then M ∪ {x} is a chain containing M, so x ∈ M
    and x ≤ u."""
    R, X = l.fixes()
    l.intros()
    Ch = chains(R, X)
    l.have(
        Exists(A, And(elem(A, Ch), ForAll(B, elem(B, Ch), A <= B, B == A))),
        by=[exists_maximal_of_tukey(Ch, X), chains_tukey(R, X)],
    )
    M, _ = l.obtain(-1)
    l.have(And(M <= X, is_chain_of(R, M)), by=[elem_chains(R, X, M)])
    l.have(Exists(u, And(elem(u, X), ForAll(x, elem(x, M), R[x, u]))))
    l.auto()
    u0, _ = l.obtain(-1)
    l.exists(u0)
    l.split()
    l.auto()
    x0 = l.fix()
    l.intros()
    M1 = M | sing(x0)
    # M ∪ {x} is a chain: m ≤ u ≤ x for m ∈ M.
    l.have(is_chain_of(R, M1))
    l.unfold(is_chain_of)
    a0, b0 = l.fixes()
    l.intros()
    l.auto(
        by=[
            zf.elem_union,
            zf.elem_sing,
            is_chain_of.defn(R, M),
            le.defn(M, X),
            partial_order_trans(R, X, a0, u0, x0),
            partial_order_trans(R, X, b0, u0, x0),
            partial_order_refl(R, X, x0),
        ]
    )
    l.have(
        elem(M1, Ch), by=[elem_chains(R, X, M1), le.defn, zf.elem_union, zf.elem_sing]
    )
    l.have(M1 == M, by=[le.defn(M, M1), zf.elem_union])
    l.have(elem(x0, M), by=[zf.elem_union, zf.elem_sing, zf.ext_ax(M1, M)])
    l.auto(by=[partial_order_antisymm(R, X, x0, u0)])
