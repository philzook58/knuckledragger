"""
Builtin theory of integers
"""

import kdrag as kd
import kdrag.smt as smt
from kdrag import prove, axiom, Theorem, define  # noqa: F401
from kdrag.smt import ForAll, Exists, Implies, And, Or, Not, If, IntVal, BoolVal  # noqa: F401

Z = smt.IntSort()
ZSet = smt.SetSort(Z)
ISet = ZSet


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
            smt.And(
                kd.QForAll([n], n >= 0, kd.QForAll([m], m >= 0, m < n, P(m)), P(n)),
                x >= 0,
            ),
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


P = smt.Const("P", ZSet)  # smt.Array("P", Z, smt.BoolSort())
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


A = smt.Const("A", ZSet)
has_ub = kd.define("ZSet.has_ub", [A, y], kd.QForAll([x], A[x], x <= y))
# closed under union,inter,etc.
# closed upward has_ub_le


is_ub = kd.define("ZSet.is_ub", [A], smt.Exists([x], has_ub(A, x)))
has_lb = kd.define("ZSet.has_lb", [A, y], kd.QForAll([x], A[x], y <= x))
is_lb = kd.define("ZSet.is_lb", [A], smt.Exists([x], has_lb(A, x)))
# has_bounds = kd.define("has_bounds", [A,x,y], smt.And(has_ub(A,x), has_lb(A,y)))
finite = kd.define("ZSet.finite", [A], smt.And(is_ub(A), is_lb(A)))


# Bijections
to_nat = define("to_nat", [n], If(n >= 0, n * 2, n * -2 - 1))
from_nat = define("from_nat", [n], If(n % 2 == 0, n / 2, -(n + 1) / 2))

to_nat_pos = prove(smt.ForAll(n, to_nat(n) >= 0), by=[to_nat.defn])
from_to_nat = prove(
    ForAll(n, from_nat(to_nat(n)) == n), by=[to_nat.defn, from_nat.defn]
)
to_from_nat = prove(
    ForAll(n, n >= 0, to_nat(from_nat(n)) == n), by=[to_nat.defn, from_nat.defn]
)

# cantor pairing
natpair = kd.define("natpair", [n, m], (n + m) * (n + m + 1) / 2 + m)
natpair_pos = prove(
    ForAll([n, m], n >= 0, m >= 0, natpair(n, m) >= 0), by=[natpair.defn]
)


natpair_succ = prove(
    ForAll([n, m], natpair(n, m) + 1 == natpair(n - 1, m + 1)),
    by=[natpair.defn],
)  # natpair(n-1,m) == natpair(n,m)
# natpair(n+1, m-1) + 1 = natpair(n, m)
natpair_zero_m = prove(
    ForAll(m, natpair(0, m) + 1 == natpair(m + 1, 0)), by=[natpair.defn]
)
# natpair(0, m-1) + 1 = natpair(m, 0)

natpair_to_tuple = smt.Function("natpair_to_tuple", Z, kd.TupleSort(Z, Z))
natpair_to_tuple = kd.define(
    "natpair_to_tuple",
    [k],
    If(
        k < 0,
        kd.tuple_(IntVal(-1), IntVal(-1)),
        If(
            k == 0,
            kd.tuple_(IntVal(0), IntVal(0)),
            If(
                natpair_to_tuple(k - 1)[0] == 0,
                kd.tuple_(natpair_to_tuple(k - 1)[1] + 1, IntVal(0)),
                kd.tuple_(
                    natpair_to_tuple(k - 1)[0] - 1, natpair_to_tuple(k - 1)[1] + 1
                ),
            ),
        ),
    ),
)

"""
@kd.PTheorem(
    ForAll(
        [n, m],
        n >= 0,
        m >= 0,
        And(
            natpair_to_tuple(natpair(n, m))[0] == n,
            natpair_to_tuple(natpair(n, m))[1] == m,
        ),
    )
)
def unpair_natpair(l):
    n, m = l.fixes()
    l.generalize(n)  # TODO: should remove from context
    m = l.induct(m)
    # n = l.fix()
    # _n = l.induct(n)
    # l.auto()
    # l.auto(by=[natpair.defn, natpair_to_tuple.defn])

    # n = l.induct(n)
    # l.auto(by=[natpair.defn, natpair_to_tuple.defn])
    # l.auto(by=[natpair.defn, natpair_to_tuple.defn])

    # l.auto(by=[natpair.defn, natpair_to_tuple.defn])

    # l.auto(by=[natpair.defn, natpair_to_tuple.defn])
"""


@kd.Theorem(
    ForAll([k], k >= 0, natpair(natpair_to_tuple(k)[0], natpair_to_tuple(k)[1]) == k)
)
def natpair_unpair(l):
    k = l.fix()
    k = l.induct(k)
    l.auto()  # k < 0
    l.auto(by=[natpair_to_tuple.defn, natpair.defn])  # k == 0

    k = l.fix()
    l.intros()
    l.case(k >= 0)
    l.unfold(natpair_to_tuple)
    l.have((k + 1 == 0) == BoolVal(False), by=[])
    l.rw(-1)
    l.have((k + 1 < 0) == BoolVal(False), by=[])
    l.rw(-1)
    l.simp()

    l.autocases()
    l.rw(-1)
    l.simp()
    l.intros()
    l.auto(by=[natpair_to_tuple.defn, natpair.defn])

    l.rw(-1)
    l.simp()
    l.intros()
    l.auto(by=[natpair_to_tuple.defn, natpair.defn])


# for i in range(9):
#    print(kd.full_simp(natpair_to_tuple(i)))

# a bijective mapping over all the integers.
pair = define("pair", [n], from_nat(natpair(to_nat(n), to_nat(m))))
