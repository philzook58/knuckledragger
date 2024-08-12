import knuckledragger as kd
import knuckledragger.smt as smt

Z = smt.IntSort()


def induct_nat(P):
    return kd.axiom(
        smt.And(P(0), kd.QForAll([n], n >= 0, P(n), P(n + 1)))
        # ---------------------------------------------------
        == kd.QForAll([n], n >= 0, P(n))
    )
