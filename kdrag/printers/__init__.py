import kdrag.smt as smt


def finsize(s: smt.SortRef):
    return s == smt.BoolSort() or isinstance(s, smt.BitVecSortRef)
