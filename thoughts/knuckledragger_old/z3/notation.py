import knuckledragger.smt as smt

smt.BoolRef.__and__ = lambda self, other: smt.And(self, other)
smt.BoolRef.__or__ = lambda self, other: smt.Or(self, other)
smt.BoolRef.__invert__ = lambda self: smt.Not(self)


# Should this be in helpers?
def QForAll(vars, hyp, conc):
    """Quantified ForAll"""
    return smt.ForAll(vars, smt.Implies(hyp, conc))


def QExists(vars, hyp, conc):
    """Quantified Exists"""
    return smt.Exists(vars, smt.And(hyp, conc))


# smt.ArrayRef.__call__ = lambda self, other: self[other]
smt.SortRef.__rshift__ = lambda self, other: smt.ArraySort(self, other)
# smt.SortRef.__mul__ = lambda self, other: smt.TupleSort(self.ctx, [self, other])

# smt.ExprRef.head = property(lambda self: self.decl().kind())
# smt.ExprRef.args = property(lambda self: [self.arg(i) for i in range(self.num_args())])
# smt.ExprRef.__match_args__ = ["head", "args"]

# smt.QuantifierRef.open_term = property(lambda self: vars = FreshConst() (return vars, subst(self.body, [])))
# smt.QuantifierRef.__match_args__ = ["open_term"]

# smt.QuantifierRef.__matmul__ = lambda self, other: smt.substitute(self.body, zip([smt.Var(n) for n in range(len(other)) , other]))
