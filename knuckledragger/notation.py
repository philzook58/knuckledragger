import z3

z3.BoolRef.__and__ = lambda self, other: z3.And(self, other)
z3.BoolRef.__or__ = lambda self, other: z3.Or(self, other)
z3.BoolRef.__invert__ = lambda self: z3.Not(self)


def QForAll(vars, hyp, conc):
    """Quantified ForAll"""
    return z3.ForAll(vars, z3.Implies(hyp, conc))


def QExists(vars, hyp, conc):
    """Quantified Exists"""
    return z3.Exists(vars, z3.And(hyp, conc))


z3.SortRef.__rshift__ = lambda self, other: z3.ArraySort(self, other)
