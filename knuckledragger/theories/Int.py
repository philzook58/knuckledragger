import knuckledragger as kd
import knuckledragger.smt as smt

Z = smt.IntSort()


def induct_nat(P):
    return kd.axiom(
        smt.And(P(0), kd.QForAll([n], n >= 0, P(n), P(n + 1)))
        # ---------------------------------------------------
        == kd.QForAll([n], n >= 0, P(n))
    )


Nat = kd.Record("Nat", ("val", Z))
x, y, z = smt.Consts("x y z", Nat)
kd.notation.wf.register(Nat, lambda x: x.val >= 0)
