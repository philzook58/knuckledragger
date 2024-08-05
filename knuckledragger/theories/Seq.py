import knuckledragger as kd
import z3

# TODO: seq needs well formedness condition inherited from elements


def induct(T: z3.SortRef, P) -> kd.kernel.Proof:
    z = z3.FreshConst(T, prefix="z")
    sort = z3.SeqSort(T)
    x, y = z3.FreshConst(sort), z3.FreshConst(sort)
    return kd.axiom(
        z3.And(
            P(z3.Empty(sort)),
            kd.QForAll([z], P(z3.Unit(z))),
            kd.QForAll([x, y], P(x), P(y), P(z3.Concat(x, y))),
        )  # -------------------------------------------------
        == kd.QForAll([x], P(x))
    )
