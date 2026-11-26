"""
Order on ω (Halmos §13): `m < n` is `m ∈ n`.

Any two natural numbers are comparable, exactly one of `m ∈ n`, `m = n`,
`n ∈ m` holds, and for distinct naturals `m ∈ n` iff `m ⊆ n`. Every nonempty
set of natural numbers has a least element.
"""

from kdrag import Theorem, define, prove
from kdrag.smt import And, Consts, Exists, ForAll, If, Not, Or
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import ZFSet, elem, le, succ, zero
from kdrag.contrib.zf.nat import (
    elem_succ,
    elem_succ_self,
    exists_eq_succ_of_ne_zero,
    induct_omega,
    is_transitive,
    nat_is_transitive,
    nat_not_elem_self,
    nat_not_le_of_elem,
    omega,
    omega_is_transitive,
    omega_succ,
    omega_zero,
    one,
    zero_ne_one,
)
from kdrag.contrib.zf.arith import (
    add,
    add_comm,
    add_elem_omega,
    add_succ,
    add_zero,
    succ_add,
    mul,
    mul_elem_omega,
    mul_succ,
    mul_zero,
    zero_add,
)

E, a, b, e, j, k, m, n, p, q = Consts("E a b e j k m n p q", ZFSet)

comparable = define("comparable", [m, n], Or(elem(m, n), m == n, elem(n, m)))

# Elements of natural numbers are natural numbers.
nat_of_elem = prove(
    ForAll([m, n], elem(n, omega), elem(m, n), elem(m, omega)),
    by=[omega_is_transitive, is_transitive.defn, le.defn],
)


@Theorem(ForAll(m, elem(m, omega), comparable(m, zero)))
def comparable_zero(l):
    """Halmos: S(0) = ω."""
    m = l.fix()
    l.intro()
    l.induct(m, using=induct_omega)
    l.auto(by=[comparable.defn])
    # m ∈ 0 is impossible; m = 0 or 0 ∈ m both give 0 ∈ m⁺.
    l.fix()
    l.auto(by=[comparable.defn, elem_succ, zero.defn, zf.elem_emp])


@Theorem(
    ForAll(
        [k, j],
        elem(k, omega),
        elem(j, omega),
        ForAll(m, elem(m, omega), comparable(m, k)),
        comparable(j, succ(k)),
        comparable(succ(j), succ(k)),
    )
)
def comparable_succ_succ(l):
    """Halmos: if S(k) = ω and j ∈ S(k⁺), then j⁺ ∈ S(k⁺)."""
    k, j = l.fixes()
    l.intros()
    l.unfold(comparable)
    l.unfold(comparable, at=-1)
    # k⁺ ∈ j or k⁺ = j give k⁺ ∈ j⁺; j = k gives j⁺ = k⁺.
    # Otherwise j ∈ k, and comparing j⁺ with k: k ∈ j⁺ would put k ∈ k,
    # so j⁺ ∈ k or j⁺ = k, and either way j⁺ ∈ k⁺.
    l.have(comparable(succ(j), k), by=[omega_succ])
    l.auto(
        by=[
            comparable.defn(succ(j), k),
            elem_succ,
            nat_is_transitive(k),
            is_transitive.defn(k),
            le.defn,
            nat_not_elem_self(k),
        ]
    )


@Theorem(ForAll([m, n], elem(m, omega), elem(n, omega), comparable(m, n)))
def nat_comparable(l):
    """Halmos: any two natural numbers are comparable, by induction on n then m."""
    m, n = l.fixes()
    l.intros()
    l.have(ForAll(m, elem(m, omega), comparable(m, n)))
    l.induct(n, using=induct_omega)
    l.auto(by=[comparable_zero])
    k = l.fix()
    l.intros()
    j = l.fix()
    l.intro()
    l.induct(j, using=induct_omega)
    l.auto(by=[comparable_zero(succ(k)), comparable.defn, omega_succ])
    j1 = l.fix()
    l.intros()
    l.auto(by=[comparable_succ_succ(k, j1)])
    l.auto()


# Exactly one of m ∈ n, m = n, n ∈ m holds.

nat_elem_trans = prove(
    ForAll([m, n, p], elem(p, omega), elem(m, n), elem(n, p), elem(m, p)),
    by=[nat_is_transitive, is_transitive.defn, le.defn],
)
nat_elem_asymm = prove(
    ForAll([m, n], elem(n, omega), elem(m, n), Not(elem(n, m))),
    by=[nat_elem_trans, nat_not_elem_self],
)


@Theorem(
    ForAll([m, n], elem(m, omega), elem(n, omega), elem(m, n) == And(m <= n, m != n))
)
def elem_iff_le_ne(l):
    """Halmos: for natural numbers, m ∈ n iff m is a proper subset of n."""
    m, n = l.fixes()
    l.intros()
    # → is transitivity of n and n ∉ n. ← : n ∈ m would make m a subset of one of
    # its elements, so by comparability m ∈ n.
    l.auto(
        by=[
            nat_is_transitive(n),
            is_transitive.defn(n),
            nat_not_elem_self(n),
            nat_comparable(m, n),
            comparable.defn(m, n),
            nat_not_le_of_elem(m),
        ]
    )


# m ≤ n

nat_le = define("nat_le", [m, n], Or(elem(m, n), m == n))

nat_le_iff_le = prove(
    ForAll([m, n], elem(m, omega), elem(n, omega), nat_le(m, n) == (m <= n)),
    by=[nat_le.defn, elem_iff_le_ne, le.defn],
)
nat_le_antisymm = prove(
    ForAll([m, n], elem(m, omega), elem(n, omega), nat_le(m, n), nat_le(n, m), m == n),
    by=[nat_le.defn, nat_elem_asymm],
)
nat_le_trans = prove(
    ForAll([m, n, p], elem(p, omega), nat_le(m, n), nat_le(n, p), nat_le(m, p)),
    by=[nat_le.defn, nat_elem_trans],
)


# Halmos §13 exercise: order is compatible with + and ·


@Theorem(ForAll([m, n], elem(n, omega), elem(m, n), elem(succ(m), succ(n))))
def succ_elem_succ(l):
    m, n = l.fixes()
    l.intros()
    # Compare m⁺ with n: n ∈ m⁺ means n ∈ m or n = m, impossible as m ∈ n.
    l.auto(
        by=[
            nat_comparable(succ(m), n),
            comparable.defn(succ(m), n),
            nat_of_elem(m, n),
            omega_succ,
            elem_succ,
            nat_elem_asymm(m, n),
            nat_not_elem_self(n),
        ]
    )


@Theorem(
    ForAll(
        [m, n, k],
        elem(m, omega),
        elem(n, omega),
        elem(k, omega),
        elem(m, n),
        elem(add(m, k), add(n, k)),
    )
)
def add_elem_add_right(l):
    m, n, k = l.fixes()
    l.intros()
    l.induct(k, using=induct_omega)
    l.auto(by=[add_zero])
    # m + j⁺ = (m + j)⁺ ∈ (n + j)⁺ = n + j⁺
    j = l.fix()
    l.auto(
        by=[
            add_succ(m, j),
            add_succ(n, j),
            succ_elem_succ(add(m, j), add(n, j)),
            add_elem_omega,
        ]
    )


@Theorem(
    ForAll(
        [m, n, k, p],
        elem(m, omega),
        elem(n, omega),
        elem(k, omega),
        elem(p, omega),
        elem(m, n),
        elem(k, p),
        elem(add(m, k), add(n, p)),
    )
)
def add_elem_add(l):
    m, n, k, p = l.fixes()
    l.intros()
    # m + k ∈ n + k = k + n ∈ p + n = n + p
    l.have(elem(add(m, k), add(n, k)), by=[add_elem_add_right(m, n, k)])
    l.have(elem(add(k, n), add(p, n)), by=[add_elem_add_right(k, p, n)])
    l.auto(
        by=[add_comm, nat_elem_trans(add(m, k), add(n, k), add(n, p)), add_elem_omega]
    )


@Theorem(
    ForAll(
        [m, n, k],
        elem(m, omega),
        elem(n, omega),
        elem(k, omega),
        elem(m, n),
        k != zero,
        elem(mul(m, k), mul(n, k)),
    )
)
def mul_elem_mul_right(l):
    m, n, k = l.fixes()
    l.intros()
    # Write k = j⁺ and induct on j.
    l.have(ForAll(j, elem(j, omega), elem(mul(m, succ(j)), mul(n, succ(j)))))
    j0 = l.fix()
    l.intro()
    l.induct(j0, using=induct_omega)
    # m·1 = m·0 + m = m
    l.auto(by=[mul_succ, mul_zero, zero_add, omega_zero])
    # m·i⁺⁺ = m·i⁺ + m ∈ n·i⁺ + n = n·i⁺⁺
    i = l.fix()
    l.intros()
    l.auto(
        by=[
            mul_succ(m, succ(i)),
            mul_succ(n, succ(i)),
            add_elem_add(mul(m, succ(i)), mul(n, succ(i)), m, n),
            mul_elem_omega,
            omega_succ,
        ]
    )
    l.auto()  # the side goal j ∈ ω left by induct
    l.auto(by=[exists_eq_succ_of_ne_zero(k)])


@Theorem(
    ForAll(
        E,
        E <= omega,
        E != zf.emp,
        Exists(k, And(elem(k, E), ForAll(m, elem(m, E), nat_le(k, m)))),
    )
)
def exists_least_of_nonempty(l):
    """Halmos §13 exercise: every nonempty set of natural numbers has a least element."""
    E = l.fix()
    l.intros()
    l.contra()
    # Suppose not. By induction, no element of any n ∈ ω is in E.
    l.have(ForAll(n, elem(n, omega), ForAll(m, elem(m, n), Not(elem(m, E)))))
    n0 = l.fix()
    l.intro()
    l.induct(n0, using=induct_omega)
    l.auto(by=[zero.defn, zf.elem_emp])
    k = l.fix()
    l.intros()
    # If k were in E it would be least: no e ∈ E lies below k, so k ≤ e by comparability.
    l.have(Not(elem(k, E)))
    l.intro()
    l.have(ForAll(m, elem(m, E), nat_le(k, m)))
    m0 = l.fix()
    l.intro()
    l.auto(
        by=[
            le.defn(E, omega),
            nat_comparable(k, m0),
            comparable.defn(k, m0),
            nat_le.defn(k, m0),
        ]
    )
    l.auto()
    l.auto(by=[elem_succ])
    l.auto()  # the side goal n ∈ ω left by induct
    # But E has an element e, and e ∈ e⁺.
    l.have(Exists(e, elem(e, E)), by=[zf.not_emp_exists_elem(E)])
    e0, _ = l.obtain(-1)
    l.have(elem(e0, omega), by=[le.defn(E, omega)])
    l.auto(by=[elem_succ_self(e0), omega_succ(e0)])


# bit(a, n) is 2n + a for a ∈ 2, as Mathlib's Nat.bit.
bit = define("bit", [a, n], If(a == zero, add(n, n), succ(add(n, n))))


@Theorem(ForAll([a, n], elem(n, omega), elem(bit(a, n), omega)))
def bit_elem_omega(l):
    a, n = l.fixes()
    l.intro()
    l.unfold(bit)
    l.auto(by=[add_elem_omega(n, n), omega_succ])


@Theorem(
    ForAll(
        [a, b, n, m],
        elem(n, omega),
        elem(m, omega),
        elem(n, m),
        elem(bit(a, n), bit(b, m)),
    )
)
def bit_elem_bit(l):
    """n < m gives 2n + 1 < 2m: as n + 1 ≤ m, 2n + 2 ≤ 2m."""
    a, b, n, m = l.fixes()
    l.intros()
    sn = succ(n)
    l.have(elem(sn, omega), by=[omega_succ])
    l.have(Or(elem(sn, m), sn == m), by=[succ_elem_succ(n, m), elem_succ(sn, m)])
    # 2(n + 1) = (2n + 1) + 1
    l.have(add(sn, sn) == succ(succ(add(n, n))), by=[add_succ(sn, n), succ_add(n, n)])
    l.have(elem(add(sn, sn), omega), by=[add_elem_omega(sn, sn)])
    l.have(elem(add(m, m), omega), by=[add_elem_omega(m, m)])
    l.have(
        Or(elem(add(sn, sn), add(m, m)), add(sn, sn) == add(m, m)),
        by=[add_elem_add(sn, m, sn, m)],
    )
    # so 2n < 2n + 1 < 2m ≤ 2m + 1.
    t = add(n, n)
    l.have(elem(succ(t), add(m, m)))
    l.auto(
        by=[elem_succ_self(succ(t)), nat_elem_trans(succ(t), add(sn, sn), add(m, m))]
    )
    l.have(
        elem(t, add(m, m)),
        by=[elem_succ_self(t), nat_elem_trans(t, succ(t), add(m, m))],
    )
    l.unfold(bit)
    l.auto(
        by=[
            elem_succ_self(add(m, m)),
            nat_elem_trans(t, add(m, m), succ(add(m, m))),
            nat_elem_trans(succ(t), add(m, m), succ(add(m, m))),
            omega_succ,
        ]
    )


@Theorem(
    ForAll(
        k,
        elem(k, omega),
        Exists(n, And(elem(n, omega), Or(k == bit(zero, n), k == bit(one, n)))),
    )
)
def exists_bit(l):
    """Every natural number is even or odd."""
    k = l.fix()
    l.intro()
    l.induct(k, using=induct_omega)
    l.exists(zero)
    l.auto(by=[omega_zero, bit.defn, add_zero(zero)])
    k1 = l.fix()
    l.intros()
    n1, _ = l.obtain(-1)
    l.cases(k1 == bit(zero, n1), k1 == bit(one, n1))
    # 2n + 1 is odd, and (2n + 1) + 1 = 2(n + 1).
    l.exists(n1)
    l.auto(by=[bit.defn, zero_ne_one])
    l.exists(succ(n1))
    l.auto(
        by=[bit.defn, omega_succ, add_succ(succ(n1), n1), succ_add(n1, n1), zero_ne_one]
    )


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
