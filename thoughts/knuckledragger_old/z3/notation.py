import z3

z3.BoolRef.__and__ = lambda self, other: z3.And(self, other)
z3.BoolRef.__or__ = lambda self, other: z3.Or(self, other)
z3.BoolRef.__invert__ = lambda self: z3.Not(self)


# Should this be in helpers?
def QForAll(vars, hyp, conc):
    """Quantified ForAll"""
    return z3.ForAll(vars, z3.Implies(hyp, conc))


def QExists(vars, hyp, conc):
    """Quantified Exists"""
    return z3.Exists(vars, z3.And(hyp, conc))


# z3.ArrayRef.__call__ = lambda self, other: self[other]
z3.SortRef.__rshift__ = lambda self, other: z3.ArraySort(self, other)
# z3.SortRef.__mul__ = lambda self, other: z3.TupleSort(self.ctx, [self, other])

# z3.ExprRef.head = property(lambda self: self.decl().kind())
# z3.ExprRef.args = property(lambda self: [self.arg(i) for i in range(self.num_args())])
# z3.ExprRef.__match_args__ = ["head", "args"]

# z3.QuantifierRef.open_term = property(lambda self: vars = FreshConst() (return vars, subst(self.body, [])))
# z3.QuantifierRef.__match_args__ = ["open_term"]

# z3.QuantifierRef.__matmul__ = lambda self, other: z3.substitute(self.body, zip([z3.Var(n) for n in range(len(other)) , other]))
