"""
Arithmetic on ω by recursion (Halmos §13).

`add(m, n)` iterates successor n times starting at m, and `mul(m, n)`
iterates "add m" n times starting at 0. Both are instances of `nat_rec`.
"""

from kdrag import Theorem, define, prove
from kdrag.smt import Consts, ForAll, Lambda
from kdrag.theories.zf.zf import ZFSet, elem, succ, zero
from kdrag.contrib.zf.nat import induct_omega, omega, omega_succ, omega_zero
from kdrag.contrib.zf.fun import app, app_elem
from kdrag.contrib.zf.rec import (
    maps_to,
    nat_rec,
    nat_rec_is_func,
    nat_rec_succ,
    nat_rec_zero,
)

k, m, n, p = Consts("k m n p", ZFSet)

# Addition

succ_fn = Lambda(k, succ(k))
maps_to_succ = prove(maps_to(succ_fn, omega), by=[maps_to.defn, omega_succ])

add = define("add", [m, n], app(nat_rec(omega, m, succ_fn), n))

add_zero = prove(
    ForAll(m, elem(m, omega), add(m, zero) == m),
    by=[add.defn, nat_rec_zero, maps_to_succ],
)
add_succ = prove(
    ForAll([m, n], elem(m, omega), elem(n, omega), add(m, succ(n)) == succ(add(m, n))),
    by=[add.defn, nat_rec_succ, maps_to_succ],
)
add_elem_omega = prove(
    ForAll([m, n], elem(m, omega), elem(n, omega), elem(add(m, n), omega)),
    by=[add.defn, nat_rec_is_func, app_elem, maps_to_succ],
)


@Theorem(ForAll(n, elem(n, omega), add(zero, n) == n))
def zero_add(l):
    n = l.fix()
    l.intro()
    l.induct(n, using=induct_omega)
    l.auto(by=[add_zero, omega_zero])
    # 0 + k⁺ = (0 + k)⁺ = k⁺
    k = l.fix()
    l.auto(by=[add_succ(zero, k), omega_zero])


@Theorem(
    ForAll([m, n], elem(m, omega), elem(n, omega), add(succ(m), n) == succ(add(m, n)))
)
def succ_add(l):
    m, n = l.fixes()
    l.intros()
    l.induct(n, using=induct_omega)
    l.auto(by=[add_zero, omega_succ])
    # m⁺ + k⁺ = (m⁺ + k)⁺ = (m + k)⁺⁺ = (m + k⁺)⁺
    k = l.fix()
    l.auto(by=[add_succ(succ(m), k), add_succ(m, k), omega_succ])


@Theorem(ForAll([m, n], elem(m, omega), elem(n, omega), add(m, n) == add(n, m)))
def add_comm(l):
    m, n = l.fixes()
    l.intros()
    l.induct(n, using=induct_omega)
    l.auto(by=[add_zero, zero_add])
    # m + k⁺ = (m + k)⁺ = (k + m)⁺ = k⁺ + m
    k = l.fix()
    l.auto(by=[add_succ(m, k), succ_add(k, m)])


@Theorem(
    ForAll(
        [m, n, p],
        elem(m, omega),
        elem(n, omega),
        elem(p, omega),
        add(add(m, n), p) == add(m, add(n, p)),
    )
)
def add_assoc(l):
    m, n, p = l.fixes()
    l.intros()
    l.induct(p, using=induct_omega)
    l.auto(by=[add_zero, add_elem_omega])
    # (m + n) + k⁺ = ((m + n) + k)⁺ = (m + (n + k))⁺ = m + (n + k)⁺ = m + (n + k⁺)
    k = l.fix()
    l.auto(
        by=[
            add_succ(add(m, n), k),
            add_succ(n, k),
            add_succ(m, add(n, k)),
            add_elem_omega,
        ]
    )


# Multiplication

maps_to_add = prove(
    ForAll(m, elem(m, omega), maps_to(Lambda(k, add(k, m)), omega)),
    by=[maps_to.defn, add_elem_omega],
)

mul = define("mul", [m, n], app(nat_rec(omega, zero, Lambda(k, add(k, m))), n))

mul_zero = prove(
    ForAll(m, elem(m, omega), mul(m, zero) == zero),
    by=[mul.defn, nat_rec_zero, maps_to_add, omega_zero],
)
mul_succ = prove(
    ForAll(
        [m, n], elem(m, omega), elem(n, omega), mul(m, succ(n)) == add(mul(m, n), m)
    ),
    by=[mul.defn, nat_rec_succ, maps_to_add, omega_zero],
)
mul_elem_omega = prove(
    ForAll([m, n], elem(m, omega), elem(n, omega), elem(mul(m, n), omega)),
    by=[mul.defn, nat_rec_is_func, app_elem, maps_to_add, omega_zero],
)


@Theorem(
    ForAll(
        [m, n, p],
        elem(m, omega),
        elem(n, omega),
        elem(p, omega),
        mul(m, add(n, p)) == add(mul(m, n), mul(m, p)),
    )
)
def mul_add(l):
    """The distributive law."""
    m, n, p = l.fixes()
    l.intros()
    l.induct(p, using=induct_omega)
    l.auto(by=[add_zero, mul_zero, mul_elem_omega])
    # m(n + k⁺) = m(n + k)⁺ = m(n + k) + m = (mn + mk) + m = mn + (mk + m) = mn + mk⁺
    k = l.fix()
    l.auto(
        by=[
            add_succ(n, k),
            mul_succ(m, add(n, k)),
            add_assoc(mul(m, n), mul(m, k), m),
            mul_succ(m, k),
            add_elem_omega,
            mul_elem_omega,
        ]
    )
