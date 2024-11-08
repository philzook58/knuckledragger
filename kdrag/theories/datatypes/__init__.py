import kdrag.smt as smt
import kdrag as kd


def induct(DT: smt.DatatypeSortRef) -> kd.Proof:
    """Build a basic induction principle for an algebraic datatype"""
    P = smt.FreshConst(smt.ArraySort(DT, smt.BoolSort()), prefix="P")
    hyps = []
    for i in range(DT.num_constructors()):
        constructor = DT.constructor(i)
        args = [
            smt.FreshConst(constructor.domain(j), prefix="a")
            for j in range(constructor.arity())
        ]
        acc = P[constructor(*args)]
        for arg in args:
            if arg.sort() == DT:
                acc = kd.QForAll([arg], P[arg], acc)
            else:
                acc = kd.QForAll([arg], acc)
        hyps.append(acc)
    x = smt.FreshConst(DT, prefix="x")
    conc = kd.QForAll([x], P[x])
    return kd.axiom(
        smt.ForAll([P], smt.Implies(smt.And(hyps), conc)), by="induction_axiom"
    )
