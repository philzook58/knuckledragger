"""
Countable sets (Halmos §23).

A set is countable when it is dominated by ω. Subsets of countable sets are
countable, and ω × ω ~ ω, through the one-to-one map

    code(0, n) = 2n,   code(m + 1, n) = 2 code(m, n) + 1,

that is, code(m, n) = 2ᵐ(2n + 1) − 1. No choice is used here; `countable_bigunion`
in `cardinal` uses it.
"""

from kdrag import Theorem, define, prove
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
from kdrag.theories.zf.zf import ZFSet, elem, le, pair, prod, succ, zero
from kdrag.contrib.zf.card import (
    dominated,
    dominated_of_le,
    dominated_trans,
    schroeder_bernstein,
)
from kdrag.contrib.zf.count import counting_theorem, ord_of
from kdrag.contrib.zf.finite import (
    bij_on_image,
    bij_on_inv,
    equivalent,
    equivalent_trans,
    finite,
    image,
    inv,
)
from kdrag.contrib.zf.ordinal import is_ordinal, omega_is_ordinal, well_order_subset
from kdrag.contrib.zf.ordset import ordinal_comparable, ordinal_le_of_elem
from kdrag.contrib.zf.poset import is_well_order, nat_le_rel, omega_well_order
from kdrag.contrib.zf.sim import is_similarity, similar
from kdrag.contrib.zf.fun import (
    app,
    bij_on,
    elem_prod_iff,
    inj_on,
    maps_to,
    pair_elem_prod,
    pfst,
    psnd,
)
from kdrag.contrib.zf.nat import (
    exists_eq_succ_of_ne_zero,
    induct_omega,
    is_transitive,
    omega,
    omega_is_transitive,
    omega_zero,
    one,
    zero_ne_one,
)
from kdrag.contrib.zf.order import bit, bit_elem_omega, bit_inj
from kdrag.contrib.zf.rec import nat_rec, nat_rec_succ, nat_rec_zero

A, B, C, X, Y, Z, a, k, m, m1, n, n1, p, q = Consts(
    "A B C X Y Z a k m m1 n n1 p q", ZFSet
)
F, G = Consts("F G", ArraySort(ZFSet, ZFSet))
R = Consts("R", ArraySort(ZFSet, ZFSet, BoolSort()))[0]

countable = define("countable", [X], dominated(X, omega))


countable_of_le = prove(
    ForAll([X, Y], Y <= X, countable(X), countable(Y)),
    by=[countable.defn, dominated_trans, dominated_of_le],
)


# n ↦ 2n + 1, iterated m times from 2n.
odd_fn = Lambda(k, bit(one, k))
maps_to_odd = prove(maps_to(odd_fn, omega, omega), by=[maps_to.defn, bit_elem_omega])
code = define("code", [m, n], app(nat_rec(omega, bit(zero, n), odd_fn), m))

code_zero = prove(
    ForAll(n, elem(n, omega), code(zero, n) == bit(zero, n)),
    by=[code.defn, nat_rec_zero, maps_to_odd, bit_elem_omega],
)
code_succ = prove(
    ForAll(
        [m, n], elem(m, omega), elem(n, omega), code(succ(m), n) == bit(one, code(m, n))
    ),
    by=[code.defn, nat_rec_succ, maps_to_odd, bit_elem_omega],
)


@Theorem(ForAll([m, n], elem(m, omega), elem(n, omega), elem(code(m, n), omega)))
def code_elem_omega(l):
    m, n = l.fixes()
    l.intros()
    l.induct(m, using=induct_omega)
    l.auto(by=[code_zero, bit_elem_omega])
    k0 = l.fix()
    l.intros()
    l.auto(by=[code_succ(k0, n), bit_elem_omega])


@Theorem(
    ForAll(
        [a, n, m1, n1],
        Or(a == zero, a == one),
        elem(n, omega),
        elem(m1, omega),
        elem(n1, omega),
        bit(a, n) == code(m1, n1),
        If(
            a == zero,
            And(m1 == zero, n == n1),
            Exists(k, And(elem(k, omega), m1 == succ(k), n == code(k, n1))),
        ),
    )
)
def bit_eq_code(l):
    """code(0, n₁) = 2n₁ is even and code(k + 1, n₁) = 2 code(k, n₁) + 1 is odd,
    so 2n + a = code(m₁, n₁) fixes the case of m₁ by the parity a."""
    a, n, m1, n1 = l.fixes()
    l.intros()
    l.cases(m1 == zero, m1 != zero)
    l.auto(by=[code_zero(n1), bit_inj(a, zero, n, n1), zero_ne_one])
    l.have(
        Exists(k, And(elem(k, omega), m1 == succ(k))),
        by=[exists_eq_succ_of_ne_zero(m1)],
    )
    k0, _ = l.obtain(-1)
    c = code(k0, n1)
    l.have(code(m1, n1) == bit(one, c), by=[code_succ(k0, n1)])
    l.have(elem(c, omega), by=[code_elem_omega(k0, n1)])
    l.have(And(a == one, n == c), by=[bit_inj(a, one, n, c)])
    l.auto(by=[zero_ne_one])


@Theorem(
    ForAll(
        m,
        elem(m, omega),
        ForAll(
            [m1, n, n1],
            elem(m1, omega),
            elem(n, omega),
            elem(n1, omega),
            code(m, n) == code(m1, n1),
            And(m == m1, n == n1),
        ),
    )
)
def code_inj(l):
    """By induction on m, with the parity cases in `bit_eq_code`."""
    m = l.fix()
    l.intro()
    l.induct(m, using=induct_omega)
    m1, n, n1 = l.fixes()
    l.intros()
    l.auto(by=[code_zero(n), bit_eq_code(zero, n, m1, n1)])
    # Step: code(k + 1, n) = 2 code(k, n) + 1 = code(m₁, n₁) gives m₁ = j + 1
    # with code(k, n) = code(j, n₁), and the hypothesis gives k = j and n = n₁.
    k1 = l.fix()
    ih = l.intros()[-1]
    m1, n, n1 = l.fixes()
    l.intros()
    c = code(k1, n)
    l.have(
        And(code(succ(k1), n) == bit(one, c), elem(c, omega)),
        by=[code_succ(k1, n), code_elem_omega(k1, n)],
    )
    l.have(
        Exists(k, And(elem(k, omega), m1 == succ(k), c == code(k, n1))),
        by=[bit_eq_code(one, c, m1, n1), zero_ne_one],
    )
    j0, _ = l.obtain(-1)
    l.specialize(ih, j0, n, n1)
    l.auto()


@Theorem(equivalent(prod(omega, omega), omega))
def prod_omega_equivalent(l):
    """Halmos §23: ω × ω ~ ω. (m, n) ↦ code(m, n) is one-to-one, and so is
    n ↦ (n, 0); Schröder-Bernstein does the rest."""
    W = prod(omega, omega)
    l.have(dominated(W, omega))
    l.unfold(dominated)
    l.exists(Lambda(p, code(pfst(p), psnd(p))))
    l.split()
    l.unfold(maps_to)
    p0 = l.fix()
    l.intro()
    l.simp()
    l.auto(by=[elem_prod_iff(omega, omega, p0), code_elem_omega])
    l.unfold(inj_on)
    p0, q0 = l.fixes()
    l.intros()
    l.simp(at=-1)
    l.auto(
        by=[
            elem_prod_iff(omega, omega, p0),
            elem_prod_iff(omega, omega, q0),
            code_inj(pfst(p0)),
        ]
    )
    l.have(dominated(omega, W))
    l.unfold(dominated)
    l.exists(Lambda(n, pair(n, zero)))
    l.unfold(maps_to)
    l.unfold(inj_on)
    l.simp()
    l.auto(by=[pair_elem_prod, omega_zero, zf.pair_inj])
    l.auto(by=[schroeder_bernstein(W, omega)])


@Theorem(ForAll([R, X], is_well_order(R, X), Not(finite(X)), dominated(omega, X)))
def omega_dominated_of_well_order(l):
    """An infinite well ordered set X is similar to an ordinal α that is not a
    natural number, so ω ⊆ α, and the inverse similarity embeds ω in X."""
    R, X = l.fixes()
    l.intros()
    a0 = ord_of(R, X)
    l.have(
        And(is_ordinal(a0), similar(R, X, nat_le_rel, a0)), by=[counting_theorem(R, X)]
    )
    l.have(Exists(G, is_similarity(G, R, X, nat_le_rel, a0)), by=[similar.defn])
    g0, _ = l.obtain(-1)
    l.have(bij_on(g0, X, a0), by=[is_similarity.defn])
    # α ∉ ω, as X ~ α is infinite; so ω ⊆ α.
    l.have(Not(elem(a0, omega)), by=[finite.defn(X), equivalent.defn(X, a0)])
    l.have(
        omega <= a0,
        by=[
            ordinal_comparable(a0, omega),
            omega_is_ordinal,
            ordinal_le_of_elem(a0, omega),
            le.defn,
        ],
    )
    l.have(bij_on(inv(g0, X), a0, X), by=[bij_on_inv(g0, X, a0)])
    l.unfold(dominated)
    l.exists(inv(g0, X))
    l.auto(by=[bij_on.defn, maps_to.defn, inj_on.defn, le.defn])


@Theorem(ForAll(X, X <= omega, Or(finite(X), equivalent(X, omega))))
def finite_or_equivalent_omega(l):
    """Halmos §23: every subset of ω is finite or equivalent to ω."""
    X = l.fix()
    l.intro()
    l.have(
        is_well_order(nat_le_rel, X),
        by=[well_order_subset(nat_le_rel, omega, X), omega_well_order],
    )
    l.cases(finite(X), Not(finite(X)))
    l.auto()
    l.have(dominated(omega, X), by=[omega_dominated_of_well_order(nat_le_rel, X)])
    l.auto(by=[schroeder_bernstein(X, omega), dominated_of_le(omega, X)])


@Theorem(ForAll(X, countable(X) == Or(finite(X), equivalent(X, omega))))
def countable_iff(l):
    """Halmos §23: a set is countable iff it is finite or equivalent to ω. A
    countable X is equivalent to its image in ω."""
    X = l.fix()
    l.split()
    l.intro()
    l.unfold(countable, at=0)
    l.unfold(dominated, at=0)
    F0, _ = l.obtain(0)
    I = image(F0, X, omega)
    l.have(I <= omega, by=[le.defn, image.defn, zf.elem_sep])
    l.have(equivalent(X, I), by=[bij_on_image(F0, X, omega), equivalent.defn])
    l.have(Or(finite(I), equivalent(I, omega)), by=[finite_or_equivalent_omega(I)])
    l.cases(finite(I), equivalent(I, omega))
    l.have(Exists(n, And(elem(n, omega), equivalent(I, n))), by=[finite.defn(I)])
    n0, _ = l.obtain(-1)
    l.auto(by=[finite.defn(X), equivalent_trans(X, I, n0)])
    l.auto(by=[equivalent_trans(X, I, omega)])
    # Conversely a natural number is a subset of ω.
    l.intro()
    l.unfold(countable)
    l.cases(finite(X), equivalent(X, omega))
    l.have(Exists(n, And(elem(n, omega), equivalent(X, n))), by=[finite.defn(X)])
    n0, _ = l.obtain(-1)
    l.have(n0 <= omega, by=[omega_is_transitive, is_transitive.defn(omega)])
    l.auto(
        by=[
            equivalent.defn(X, n0),
            bij_on.defn,
            dominated.defn,
            dominated_of_le(omega, n0),
            dominated_trans(X, n0, omega),
        ]
    )
    l.auto(by=[equivalent.defn(X, omega), bij_on.defn, dominated.defn])
