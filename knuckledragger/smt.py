import os

Z3SOLVER = "z3"
CVC5SOLVER = "cvc5"
solver = os.getenv("KNUCKLE_SOLVER")
if solver is None or solver == Z3SOLVER:
    solver = "z3"
    from z3 import *
elif solver == CVC5SOLVER:
    import cvc5
    from cvc5.pythonic import *

    Z3PPObject = object
    FuncDecl = FuncDeclRef

    class Solver(cvc5.pythonic.Solver):
        def __init__(self):
            super().__init__()
            self.set("produce-unsat-cores", "true")

        def set(self, option, value):
            if option == "timeout":
                self.set("tlimit-per", value)
            else:
                super().set(option, value)

        def assert_and_track(self, thm, name):
            x = Bool(name)
            self.add(x)
            return self.add(Implies(x, thm))

        def unsat_core(self):
            return [cvc5.pythonic.BoolRef(x) for x in self.solver.getUnsatCore()]

    def Const(name, sort):
        # _to_expr doesn't have a DatatypeRef case
        x = cvc5.pythonic.Const(name, sort)
        if isinstance(sort, DatatypeSortRef):
            x = DatatypeRef(x.ast, x.ctx, x.reverse_children)
        return x

    def Consts(names, sort):
        return [Const(name, sort) for name in names.split()]

    def _qsort(self):
        if self.is_lambda():
            return ArraySort(self.var_sort(0), self.body().sort())
        else:
            return BoolSort(self.ctx)

    QuantifierRef.sort = _qsort
else:
    raise ValueError(
        "Unknown solver in environment variable KNUCKLE_SOLVER: {}".format(solver)
    )
