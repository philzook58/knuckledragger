import kdrag.smt as smt


def of_sort(s: smt.SortRef):
    if s == smt.BoolSort():
        return "bool"
    if isinstance(s, smt.BitVecSortRef):
        if s.size() in [8, 16, 32, 64]:
            return f"u{s.size()}"
        else:
            raise NotImplementedError("No support for arbitrary C int sizes", s.size())
    else:
        raise NotImplementedError(f"Cannot convert {s} to C type")
