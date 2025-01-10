"""
Reexported z3 functionality <https://z3prover.github.io/api/html/namespacez3py.html>
This is a shim file to enable the use of cvc5 and vampire as default solvers.
This is controlled by setting the environment variable KNUCKLE_SOLVER to "cvc5" or "vampire" before importing knuckledragger.
"""

import os
from . import config

Z3SOLVER = "z3"
CVC5SOLVER = "cvc5"
VAMPIRESOLVER = "vampire"
solver = os.getenv("KNUCKLE_SOLVER")

if solver is None or solver == Z3SOLVER:
    solver = "z3"
    import z3
    from z3 import *

    _py2expr = z3.z3._py2expr

    def is_if(x: z3.ExprRef) -> bool:
        """
        Check if an expression is an if-then-else.
        >>> is_if(z3.If(True, 1, 2))
        True
        """
        return z3.is_app_of(x, z3.Z3_OP_ITE)

    def is_constructor(x: z3.ExprRef) -> bool:
        """
        Check if an expression is a constructor.
        >>> Color = z3.Datatype("Color")
        >>> Color.declare("red")
        >>> Color = Color.create()
        >>> is_constructor(Color.red)
        True
        """
        return z3.is_app_of(x, z3.Z3_OP_DT_CONSTRUCTOR)

    def is_accessor(x: z3.ExprRef) -> bool:
        """
        Check if an expression is an accessor.
        >>> Color = z3.Datatype("Color")
        >>> Color.declare("red", ("r", z3.IntSort()))
        >>> Color = Color.create()
        >>> is_accessor(Color.r(Color.red(3)))
        True
        """
        return z3.is_app_of(x, z3.Z3_OP_DT_ACCESSOR)

    def is_recognizer(x: z3.ExprRef) -> bool:
        """
        Check if recognizer.
        >>> Color = z3.Datatype("Color")
        >>> Color.declare("red")
        >>> Color = Color.create()
        >>> is_recognizer(Color.is_red(Color.red))
        True
        """
        return z3.is_app_of(x, z3.Z3_OP_DT_IS)

    def is_power(x: z3.ExprRef) -> bool:
        """
        Check if an expression is a power.
        >>> x = z3.Real("x")
        >>> is_power(x**3)
        True
        """
        return z3.is_app_of(x, z3.Z3_OP_POWER)

    Z3Solver = Solver
elif solver == VAMPIRESOLVER:
    from z3 import *
    from kdrag.solvers import VampireSolver

    Z3Solver = Solver
    Solver = VampireSolver


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

config.solver = Solver


def Eq(x, y):
    """Python __eq__ resolution rules flips the order if y is a subclass of x.
    This function corrects that."""
    e = x == y
    if type(x) is not type(y) and issubclass(type(y), type(x)):
        return e.decl()(e.arg(1), e.arg(0))
    else:
        return e
