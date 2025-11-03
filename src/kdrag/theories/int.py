"""
Builtin theory of integers
"""

import kdrag as kd
import kdrag.smt as smt

Z = smt.IntSort()


def induct_nat(x, P):
    n = smt.FreshConst(Z, prefix="n")
    return kd.axiom(
        smt.Implies(
            smt.And(P(0), kd.QForAll([n], n >= 0, P(n), P(n + 1)), x >= 0),
            # ---------------------------------------------------
            P(x),
        )
    )


n, x, N = smt.Ints("n x N")
P = smt.Array("P", Z, smt.BoolSort())
_l = kd.Lemma(
    kd.QForAll(
        [P],
        P(0),
        kd.QForAll([n], n >= 0, P(n), P(n + 1)),
        kd.QForAll([x], x >= 0, P(x)),
    ),
)
_P = _l.fix()
_l.intros()
_x = _l.fix()
_l.intros()
_l.induct(_x, using=induct_nat)
induct_nat_ax = _l.qed()


def induct_nat_strong(x, P):
    n = smt.FreshConst(Z, prefix="n")
    m = smt.FreshConst(Z, prefix="m")
    return kd.axiom(
        smt.Implies(
            kd.QForAll([n], n >= 0, kd.QForAll([m], m >= 0, m < n, P(m)), P(n), x >= 0),
            # ---------------------------------------------------
            P(x),
        )
    )


induct = kd.notation.induct_int


x, y, z = smt.Ints("x y z")
even = kd.define("even", [x], smt.Exists([y], x == 2 * y))
odd = kd.define("odd", [x], smt.Exists([y], x == 2 * y + 1))

n, m, k = smt.Ints("n m k")
add_comm = kd.prove(smt.ForAll([n, m], n + m == m + n))
add_assoc = kd.prove(smt.ForAll([n, m, k], n + (m + k) == (n + m) + k))
add_zero = kd.prove(smt.ForAll([n], n + 0 == n))
add_inv = kd.prove(smt.ForAll([n], n + -n == 0))

add_monotone = kd.prove(kd.QForAll([n, m, k], n <= m, n + k <= m + k))

mul_comm = kd.prove(smt.ForAll([n, m], n * m == m * n))
mul_assoc = kd.prove(smt.ForAll([n, m, k], n * (m * k) == (n * m) * k))
mul_one = kd.prove(smt.ForAll([n], n * 1 == n))
mul_zero = kd.prove(smt.ForAll([n], n * 0 == 0))

mul_monotone = kd.prove(kd.QForAll([n, m, k], n <= m, k >= 0, n * k <= m * k))


le_refl = kd.prove(smt.ForAll([n], n <= n))
le_trans = kd.prove(kd.QForAll([n, m, k], n <= m, m <= k, n <= k))


lt_trans = kd.prove(kd.QForAll([n, m, k], n < m, m < k, n < k))
lt_total = kd.prove(kd.QForAll([n, m], smt.Or(n < m, n == m, m < n)))


distrib_left = kd.prove(smt.ForAll([n, m, k], n * (m + k) == n * m + n * k))
distrib_right = kd.prove(smt.ForAll([n, m, k], (m + k) * n == m * n + k * n))


# TODO: Generic facilities for choose
# https://en.wikipedia.org/wiki/Epsilon_calculus
choose = smt.Function("choose", smt.ArraySort(Z, smt.BoolSort()), Z)
P = smt.Const("P", smt.ArraySort(Z, smt.BoolSort()))
choose_ax = kd.axiom(smt.ForAll([P], P[choose(P)] == smt.Exists([n], P[n])))

NatI = kd.Struct("NatI", ("val", Z))
n, m, k = smt.Consts("n m k", NatI)
kd.notation.wf.register(NatI, lambda x: x.val >= 0)


n, m, p, q = smt.Ints("n m p q")
prime = kd.define(
    "prime",
    [n],
    smt.And(n > 1, smt.Not(smt.Exists([p, q], smt.And(p > 1, q > 1, n == p * q)))),
)
dvd = kd.define("dvd", [n, m], smt.Exists([p], m == n * p))
fact = smt.Function("fact", smt.IntSort(), smt.IntSort())
fact = kd.define("fact", [n], smt.If(n <= 0, 1, n * fact(n - 1)))

n, k = kd.FreshVars("n k", Z)
prime_nat = kd.prove(smt.Implies(prime(n), n >= 0), by=prime.defn(n)).forall([n])

prime_gt_1 = kd.prove(smt.Implies(prime(n), n > 1), by=prime.defn(n)).forall([n])


dvd_imp_le = kd.prove(
    smt.Implies(smt.And(dvd(k, n), k >= 0, n > 0), k <= n), unfold=1
).forall([k, n])


_l = kd.Lemma(fact(n) >= 1)
_l.induct(n)
_l.unfold(fact)
_l.auto()
_l.auto(unfold=1)
_n = _l.fix()
_l.intros()
_l.simp()
_l.unfold(fact)
_l.simp()
_l.auto()
fact_ge_1 = _l.qed().forall([n])

m = kd.FreshVar("m", smt.IntSort())

_l = kd.Lemma(smt.Implies(smt.And(1 <= m, m <= n), dvd(m, fact(n))))
_l.induct(n)
# inductive case n < 0 is vacuous
_l.auto()
# inductive case n == 0
_l.auto(by=[fact.defn(smt.IntVal(0))])
# inductive case n > 0
_l.unfold(dvd)
_n = _l.fix()
_l.intros()
_l.unfold(fact)
_l.simp()
_l.intros()
_l.simp(at=0)
_l.cases(m == _n + 1)
# case m == 1 + _n
_l.auto()
# case m != 1 + _n
_l.have(smt.Exists([p], fact(_n) == m * p), by=[])
_p = _l.obtain(3)
_l.exists(_p * (_n + 1))
_l.auto()
dvd_fact = _l.qed().forall([m, n])


P = smt.Array("P", Z, smt.BoolSort())
search = kd.define("search", [P, n], smt.If(P[n], n, smt.If(P[-n], -n, P[n + 1])))
choose = kd.notation.choose.define([P], search(P, 0))
# A choice operator. Also a relative of Kleene Mu
# https://en.wikipedia.org/wiki/%CE%9C_operator


# undef_downsearch = smt.FreshFunction(
#    "undef_downsearch", smt.ArraySort(Z, smt.BoolSort())
# )
downsearch = smt.Function("downsearch", smt.ArraySort(Z, smt.BoolSort()), Z, Z)
downsearch = kd.define(
    "downsearch",
    [P, n],
    smt.If(P[n], n, smt.If(n < 0, 0, downsearch(P, n - 1))),
)
bchoose = kd.define(
    "bchoose", [P, N], downsearch(P, N)
)  # Default to 0 if no n satisfies P[n]

# 0 <= bchoose() <= N
bexists = kd.define("bexists", [P, N], P[bchoose(P, N)])
