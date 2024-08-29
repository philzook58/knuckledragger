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


Nat = kd.Record("Nat", ("val", Z))
n, m, k = smt.Consts("n m k", Nat)
kd.notation.wf.register(Nat, lambda x: x.val >= 0)
