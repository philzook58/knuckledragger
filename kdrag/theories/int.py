import kdrag as kd
import kdrag.smt as smt

Z = smt.IntSort()


def induct_nat(P):
    n = smt.FreshConst(Z, prefix="n")
    return kd.axiom(
        smt.And(P(0), kd.QForAll([n], n >= 0, P(n), P(n + 1)))
        # ---------------------------------------------------
        == kd.QForAll([n], n >= 0, P(n))
    )


def induct(x):
    n = smt.FreshConst(Z, prefix="n")
    P = smt.FreshConst(smt.ArraySort(Z, smt.BoolSort()), prefix="P")
    return kd.axiom(
        kd.QForAll(
            [P],
            smt.And(
                P[0],
                kd.QForAll([n], n >= 0, P[n], P[n + 1]),
                kd.QForAll([n], n <= 0, P[n], P[n - 1]),
            )
            # ---------------------------------------------------
            == P[x],
        ),
        by="integer_induction",
    )


kd.notation.induct.register(Z, induct)

NatI = kd.Record("NatI", ("val", Z))
n, m, k = smt.Consts("n m k", NatI)
kd.notation.wf.register(NatI, lambda x: x.val >= 0)
