import kdrag as kd
import kdrag.smt as smt

"""
Built in smtlib theory of finite sequences.
"""
# TODO: seq needs well formedness condition inherited from elements


def induct(T: smt.SortRef, P) -> kd.kernel.Proof:
    z = smt.FreshConst(T, prefix="z")
    sort = smt.SeqSort(T)
    x, y = smt.FreshConst(sort), smt.FreshConst(sort)
    return kd.axiom(
        smt.And(
            P(smt.Empty(sort)),
            kd.QForAll([z], P(smt.Unit(z))),
            kd.QForAll([x, y], P(x), P(y), P(smt.Concat(x, y))),
        )  # -------------------------------------------------
        == kd.QForAll([x], P(x))
    )
