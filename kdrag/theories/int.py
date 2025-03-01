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


n, x = smt.Ints("n x")
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


def induct(x, P):
    n = smt.FreshConst(Z, prefix="n")
    # P = smt.FreshConst(smt.ArraySort(Z, smt.BoolSort()), prefix="P")
    return kd.axiom(
        smt.Implies(
            smt.And(
                kd.QForAll([n], n <= 0, P[n], P[n - 1]),
                P(0),
                kd.QForAll([n], n >= 0, P[n], P[n + 1]),
            ),
            # ---------------------------------------------------
            P(x),
        ),
        by="integer_induction",
    )


kd.notation.induct.register(Z, induct)

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
