"""
Countable sets (Halmos §23).

A set is countable when it is dominated by ω. Subsets of countable sets are
countable, and ω × ω ~ ω, through the one-to-one map

    code(0, n) = 2n,   code(m + 1, n) = 2 code(m, n) + 1,

that is, code(m, n) = 2ᵐ(2n + 1) − 1. No choice is used here; `countable_union`
in `cardinal` uses it.
"""

from kdrag import Theorem, define, prove
from kdrag.smt import And, ArraySort, BoolSort, Not, Consts, Exists, ForAll, Lambda, Or
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import ZFSet, elem, le, pair, prod, succ, zero
from kdrag.contrib.zf.arith import add, add_elem_omega
from kdrag.contrib.zf.card import dominated, schroeder_bernstein
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
from kdrag.contrib.zf.ordinal import is_ordinal, omega_is_ordinal
from kdrag.contrib.zf.ordset import ordinal_comparable, ordinal_le_of_elem
from kdrag.contrib.zf.poset import is_well_order, nat_le_rel, omega_well_order
from kdrag.contrib.zf.ordinal import well_order_subset
from kdrag.contrib.zf.sim import is_similarity, similar
from kdrag.contrib.zf.fun import (
    app,
    bij_on,
    inj_on,
    maps_to,
    pair_elem_prod,
    pfst,
    psnd,
)
from kdrag.contrib.zf.nat import (
    elem_succ_self,
    exists_eq_succ_of_ne_zero,
    induct_omega,
    nat_not_elem_self,
    omega,
    omega_is_transitive,
    is_transitive,
    omega_zero,
)
from kdrag.contrib.zf.oarith import one, zero_ne_one
from kdrag.contrib.zf.omul import bit, bit_elem_bit, bit_elem_omega, elem_prod_iff
from kdrag.contrib.zf.order import comparable, nat_comparable
from kdrag.contrib.zf.rec import nat_rec, nat_rec_succ, nat_rec_zero

A, B, C, X, Y, Z, k, m, m1, n, n1, p, q = Consts("A B C X Y Z k m m1 n n1 p q", ZFSet)
F, G = Consts("F G", ArraySort(ZFSet, ZFSet))
R = Consts("R", ArraySort(ZFSet, ZFSet, BoolSort()))[0]

countable = define("countable", [X], dominated(X, omega))


@Theorem(ForAll([X, Y, Z], dominated(X, Y), dominated(Y, Z), dominated(X, Z)))
def dominated_trans(l):
    """Compose the one-to-one maps."""
    X, Y, Z = l.fixes()
    l.intros()
    l.unfold(dominated, at=0)
    l.unfold(dominated, at=1)
    F0, _ = l.obtain(0)
    G0, _ = l.obtain(1)
    l.unfold(dominated)
    l.exists(Lambda(k, G0[F0[k]]))
    l.auto(by=[maps_to.defn, inj_on.defn])


@Theorem(ForAll([X, Y], Y <= X, dominated(Y, X)))
def dominated_of_le(l):
    X, Y = l.fixes()
    l.intro()
    l.unfold(dominated)
    l.exists(Lambda(k, k))
    l.auto(by=[maps_to.defn, inj_on.defn, le.defn])


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
        [m, n],
        elem(m, omega),
        elem(n, omega),
        code(succ(m), n) == bit(one, code(m, n)),
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
        [p, q, n, m],
        elem(n, omega),
        elem(m, omega),
        Or(p == zero, p == one),
        Or(q == zero, q == one),
        bit(p, n) == bit(q, m),
        And(p == q, n == m),
    )
)
def bit_inj(l):
    """2n + a determines n and a: different n are ordered, and 2n < 2n + 1."""
    p, q, n, m = l.fixes()
    l.intros()
    l.have(
        Or(elem(n, m), n == m, elem(m, n)),
        by=[nat_comparable(n, m), comparable.defn(n, m)],
    )
    # For n = m, 2n ≠ 2n + 1 as 2n ∉ 2n.
    t = add(n, n)
    l.auto(
        by=[
            bit_elem_bit(p, q, n, m),
            bit_elem_bit(q, p, m, n),
            nat_not_elem_self(bit(p, n)),
            bit_elem_omega(p, n),
            bit.defn,
            nat_not_elem_self(t),
            elem_succ_self(t),
            add_elem_omega(n, n),
            zero_ne_one,
        ]
    )


def _bits(a, n):
    return [bit_inj(a, zero, n, n1), bit_inj(a, one, n, n1)]


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
    """By induction on m: code(0, n) is even and code(m + 1, n) is odd, and
    2a + 1 = 2b + 1 gives a = b."""
    m = l.fix()
    l.intro()
    l.induct(m, using=induct_omega)
    m1, n, n1 = l.fixes()
    l.intros()
    l.cases(m1 == zero, m1 != zero)
    l.auto(by=[code_zero, bit_inj(zero, zero, n, n1)])
    l.have(
        Exists(k, And(elem(k, omega), m1 == succ(k))),
        by=[exists_eq_succ_of_ne_zero(m1)],
    )
    k0, _ = l.obtain(-1)
    c = code(k0, n1)
    l.auto(
        by=[
            code_zero(n),
            code_succ(k0, n1),
            code_elem_omega(k0, n1),
            bit_inj(zero, one, n, c),
            zero_ne_one,
        ]
    )
    # Step: code(k + 1, n) = 2 code(k, n) + 1 is odd.
    k1 = l.fix()
    l.intros()
    m1, n, n1 = l.fixes()
    l.intros()
    c = code(k1, n)
    l.have(code(succ(k1), n) == bit(one, c), by=[code_succ(k1, n)])
    l.have(elem(c, omega), by=[code_elem_omega(k1, n)])
    l.cases(m1 == zero, m1 != zero)
    l.auto(by=[code_zero(n1), bit_inj(one, zero, c, n1), zero_ne_one])
    l.have(
        Exists(k, And(elem(k, omega), m1 == succ(k))),
        by=[exists_eq_succ_of_ne_zero(m1)],
    )
    j0, _ = l.obtain(-1)
    c1 = code(j0, n1)
    l.have(
        c == c1,
        by=[code_succ(j0, n1), code_elem_omega(j0, n1), bit_inj(one, one, c, c1)],
    )
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
