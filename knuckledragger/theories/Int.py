import knuckledragger as kd
import z3

Z = z3.IntSort()


def induct_nat(P):
    return kd.axiom(
        z3.And(P(0), kd.QForAll([n], n >= 0, P(n), P(n + 1)))
        # ---------------------------------------------------
        == kd.QForAll([n], n >= 0, P(n))
    )
