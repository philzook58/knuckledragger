"""
Builtin theory of integers
"""

import kdrag as kd
from kdrag import (  # noqa: F401
    FreshVar,
    FreshVars,
    QForAll,
    Struct,
    Theorem,
    axiom,
    define,
    prove,
    tuple_,
)
from kdrag.smt import (  # noqa: F401
    And,
    Array,
    ArraySort,
    BoolSort,
    BoolVal,
    Const,
    Consts,
    Exists,
    ForAll,
    FreshConst,
    Function,
    If,
    Implies,
    Int,
    IntSort,
    IntVal,
    Ints,
    Not,
    Or,
    SetSort,
)

Z = IntSort()
ZSet = SetSort(Z)
ISet = ZSet


def induct_nat(x, P):
    n = FreshConst(Z, prefix="n")
    return axiom(
        Implies(
            And(P(0), QForAll([n], n >= 0, P(n), P(n + 1)), x >= 0),
            # ---------------------------------------------------
            P(x),
        )
    )


n, x, N = Ints("n x N")
P = Array("P", Z, BoolSort())


@Theorem(
    QForAll(
        [P],
        P(0),
        QForAll([n], n >= 0, P(n), P(n + 1)),
        QForAll([x], x >= 0, P(x)),
    )
)
def induct_nat_ax(l):
    _P = l.fix()
    l.intros()
    l.intros()
    _x = l.fix()
    l.intros()
    l.induct(_x, using=induct_nat)


def induct_nat_strong(x, P):
    n = FreshConst(Z, prefix="n")
    m = FreshConst(Z, prefix="m")
    return axiom(
        Implies(
            And(
                QForAll([n], n >= 0, QForAll([m], m >= 0, m < n, P(m)), P(n)),
                x >= 0,
            ),
            # ---------------------------------------------------
            P(x),
        )
    )


induct = kd.notation.induct_int

t = Int("t")


@Theorem(
    ForAll(
        [P, t],
        t >= 0,
        P(0),
        P(1),
        ForAll([t], t >= 0, P(t), P(t + 1), P(t + 2)),
        And(P(t), P(t + 1)),
    )
)
def induct2_pair(l):
    P, t = l.fixes()
    l.induct(t)
    l.auto()
    l.auto()
    l.auto()


@Theorem(
    ForAll(
        [P, t], t >= 0, P(0), P(1), ForAll([t], t >= 0, P(t), P(t + 1), P(t + 2)), P(t)
    )
)
def induct2(l):
    P, t = l.fixes()
    l.auto(by=induct2_pair(P, t))


x, y, z = Ints("x y z")
even = define("even", [x], Exists([y], x == 2 * y))
odd = define("odd", [x], Exists([y], x == 2 * y + 1))

n, m, k = Ints("n m k")
add_comm = prove(ForAll([n, m], n + m == m + n))
add_assoc = prove(ForAll([n, m, k], n + (m + k) == (n + m) + k))
add_zero = prove(ForAll([n], n + 0 == n))
add_inv = prove(ForAll([n], n + -n == 0))

add_monotone = prove(QForAll([n, m, k], n <= m, n + k <= m + k))

mul_comm = prove(ForAll([n, m], n * m == m * n))
mul_assoc = prove(ForAll([n, m, k], n * (m * k) == (n * m) * k))
mul_one = prove(ForAll([n], n * 1 == n))
mul_zero = prove(ForAll([n], n * 0 == 0))

mul_monotone = prove(QForAll([n, m, k], n <= m, k >= 0, n * k <= m * k))


le_refl = prove(ForAll([n], n <= n))
le_trans = prove(QForAll([n, m, k], n <= m, m <= k, n <= k))


lt_trans = prove(QForAll([n, m, k], n < m, m < k, n < k))
lt_total = prove(QForAll([n, m], Or(n < m, n == m, m < n)))


distrib_left = prove(ForAll([n, m, k], n * (m + k) == n * m + n * k))
distrib_right = prove(ForAll([n, m, k], (m + k) * n == m * n + k * n))


# TODO: Generic facilities for choose
# https://en.wikipedia.org/wiki/Epsilon_calculus
choose = Function("choose", ArraySort(Z, BoolSort()), Z)
P = Const("P", ArraySort(Z, BoolSort()))
choose_ax = axiom(ForAll([P], P[choose(P)] == Exists([n], P[n])))

NatI = Struct("NatI", ("val", Z))
n, m, k = Consts("n m k", NatI)
kd.notation.wf.register(NatI, lambda x: x.val >= 0)


n, m, p, q = Ints("n m p q")
prime = define(
    "prime",
    [n],
    And(n > 1, Not(Exists([p, q], And(p > 1, q > 1, n == p * q)))),
)
dvd = define("dvd", [n, m], Exists([p], m == n * p))
fact = Function("fact", IntSort(), IntSort())
fact = define("fact", [n], If(n <= 0, 1, n * fact(n - 1)))

n, k = FreshVars("n k", Z)


@Theorem(ForAll(n, Implies(prime(n), n >= 0)))
def prime_nat(l):
    n = l.fix()
    l.auto(by=prime.defn(n))


@Theorem(ForAll(n, Implies(prime(n), n > 1)))
def prime_gt_1(l):
    n = l.fix()
    l.auto(by=prime.defn(n))


dvd_imp_le = prove(
    ForAll([k, n], Implies(And(dvd(k, n), k >= 0, n > 0), k <= n)), unfold=1
)


@Theorem(ForAll(n, fact(n) >= 1))
def fact_ge_1(l):
    n = l.fix()
    l.induct(n)
    l.unfold(fact)
    l.auto()
    l.auto(unfold=1)
    _n = l.fix()
    l.intros()
    l.intros()
    l.simp()
    l.unfold(fact)
    l.simp()
    l.auto()


m = FreshVar("m", IntSort())


@Theorem(ForAll([m, n], Implies(And(1 <= m, m <= n), dvd(m, fact(n)))))
def dvd_fact(l):
    m, n = l.fixes()
    l.induct(n)
    # inductive case n < 0 is vacuous
    l.auto()
    # inductive case n == 0
    l.auto(by=[fact.defn(IntVal(0))])
    # inductive case n > 0
    l.unfold(dvd)
    _n = l.fix()
    l.intros()
    l.intros()
    l.unfold(fact)
    l.simp()
    l.intros()
    l.simp(at=1)
    l.cases(m == _n + 1)
    # case m == 1 + _n
    l.auto()
    # case m != 1 + _n
    witness = l.have(Exists([p], fact(_n) == m * p), by=[])
    _p = l.obtain(witness)
    l.exists(_p * (_n + 1))
    l.auto()


P = Const("P", ZSet)  # smt.Array("P", Z, smt.BoolSort())
search = define("search", [P, n], If(P[n], n, If(P[-n], -n, P[n + 1])))
choose = kd.notation.choose.define([P], search(P, 0))
# A choice operator. Also a relative of Kleene Mu
# https://en.wikipedia.org/wiki/%CE%9C_operator


# undef_downsearch = smt.FreshFunction(
#    "undef_downsearch", smt.ArraySort(Z, smt.BoolSort())
# )
downsearch = Function("downsearch", ArraySort(Z, BoolSort()), Z, Z)
downsearch = define(
    "downsearch",
    [P, n],
    If(P[n], n, If(n < 0, 0, downsearch(P, n - 1))),
)
bchoose = define(
    "bchoose", [P, N], downsearch(P, N)
)  # Default to 0 if no n satisfies P[n]

# 0 <= bchoose() <= N
bexists = define("bexists", [P, N], P[bchoose(P, N)])


A = Const("A", ZSet)
has_ub = define("ZSet.has_ub", [A, y], QForAll([x], A[x], x <= y))
# closed under union,inter,etc.
# closed upward has_ub_le


is_ub = define("ZSet.is_ub", [A], Exists([x], has_ub(A, x)))
has_lb = define("ZSet.has_lb", [A, y], QForAll([x], A[x], y <= x))
is_lb = define("ZSet.is_lb", [A], Exists([x], has_lb(A, x)))
# has_bounds = kd.define("has_bounds", [A,x,y], smt.And(has_ub(A,x), has_lb(A,y)))
finite = define("ZSet.finite", [A], And(is_ub(A), is_lb(A)))


# Bijections
to_nat = define("to_nat", [n], If(n >= 0, n * 2, n * -2 - 1))
from_nat = define("from_nat", [n], If(n % 2 == 0, n / 2, -(n + 1) / 2))

to_nat_pos = prove(ForAll(n, to_nat(n) >= 0), by=[to_nat.defn])
from_to_nat = prove(
    ForAll(n, from_nat(to_nat(n)) == n), by=[to_nat.defn, from_nat.defn]
)
to_from_nat = prove(
    ForAll(n, n >= 0, to_nat(from_nat(n)) == n), by=[to_nat.defn, from_nat.defn]
)

# cantor pairing
natpair = define("natpair", [n, m], (n + m) * (n + m + 1) / 2 + m)
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

natpair_to_tuple = Function("natpair_to_tuple", Z, kd.TupleSort(Z, Z))
natpair_to_tuple = define(
    "natpair_to_tuple",
    [k],
    If(
        k < 0,
        tuple_(IntVal(-1), IntVal(-1)),
        If(
            k == 0,
            tuple_(IntVal(0), IntVal(0)),
            If(
                natpair_to_tuple(k - 1)[0] == 0,
                tuple_(natpair_to_tuple(k - 1)[1] + 1, IntVal(0)),
                tuple_(natpair_to_tuple(k - 1)[0] - 1, natpair_to_tuple(k - 1)[1] + 1),
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


@Theorem(
    ForAll([k], k >= 0, natpair(natpair_to_tuple(k)[0], natpair_to_tuple(k)[1]) == k)
)
def natpair_unpair(l):
    k = l.fix()
    k = l.induct(k)
    l.auto()  # k < 0
    l.auto(by=[natpair_to_tuple.defn, natpair.defn])  # k == 0

    k = l.fix()
    l.intros()
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
