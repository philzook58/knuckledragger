# type: ignore
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

    def is_neg(x: z3.ExprRef) -> bool:
        """
        Check if an expression is a negation.
        >>> x = z3.Int("x")
        >>> is_neg(-x)
        True
        """
        return z3.is_app_of(x, z3.Z3_OP_UMINUS)

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

    def is_uninterp(x: z3.ExprRef) -> bool:
        """
        Check if uninterpreted function.
        >>> x = z3.Real("x")
        >>> f = z3.Function("f", RealSort(), RealSort())
        >>> is_uninterp(x)
        True
        >>> is_uninterp(f(x))
        True
        >>> is_uninterp(x + 1)
        False
        >>> is_uninterp(z3.RealVal(42.1))
        False
        """
        return z3.is_app_of(x, z3.Z3_OP_UNINTERPRETED)

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

RawEq = ExprRef.__eq__


def Eq(x, y):
    """Python __eq__ resolution rules flips the order if y is a subclass of x.
    This function corrects that.

    >>> IntVal(1) + IntVal(2) == IntVal(3)
    3 == 1 + 2
    >>> Eq(IntVal(1) + IntVal(2), IntVal(3))
    1 + 2 == 3
    """
    return RawEq(x, y)


NEq = ExprRef.__ne__

# TODO: Overload them?
RawForAll = ForAll
RawExists = Exists

ExprRef.induct = lambda x, P: None
ExprRef.__add__ = lambda x, y: None
ExprRef.__sub__ = lambda x, y: None

FuncDeclRef.defn = None

"""
Caching.
The CFFI interface to z3 is very costly. Caching calls can help some of that pain.
"""


AstRef._cache_id = None
get_id_orig = AstRef.get_id


def get_id(self):
    if self._cache_id is None:
        self._cache_id = get_id_orig(self)
    return self._cache_id


AstRef.get_id = get_id
ExprRef.get_id = get_id
FuncDeclRef.get_id = get_id


def eq(x, y):
    return x.get_id() == y.get_id()


AstRef.eq = eq
AstRef.__hash__ = lambda x: hash(x.get_id())
SortRef.__eq__ = eq
FuncDeclRef.__eq__ = eq
SortRef.__ne__ = lambda x, y: not eq(x, y)
FuncDeclRef.__ne__ = lambda x, y: not eq(x, y)


decl_orig = ExprRef.decl
ExprRef._cache_decl = None

# Caching of decls so they can be tagged with properties
# TODO: There are other ways of getting decls, so this is not a complete cache.
decls: dict[int, FuncDeclRef] = {}


def decl(self):
    if self._cache_decl is None:
        decl = decl_orig(self)
        self._cache_decl = decl
    else:
        decl = self._cache_decl
    id_ = decl.get_id()
    if id_ in decls:
        return decls[id_]
    else:
        decls[id_] = decl
        return decl


OldFunction = Function


def Function(*args, **kwargs):
    decl = OldFunction(*args, **kwargs)
    if decl.get_id() not in decls:
        decls[decl.get_id()] = decl
    else:
        decl = decls[decl.get_id()]
    return decl


ExprRef.decl = decl

ExprRef._cache_args = None
old_arg = ExprRef.arg


def arg(self, i):
    if self._cache_args is None:
        self._cache_args = {}
    a = self._cache_args.get(i, None)
    if a is None:
        a = old_arg(self, i)
        self._cache_args[i] = a  # old_arg(self, i)
    return a


ExprRef.arg = arg

ExprRef._cache_num_args = None

num_args_orig = ExprRef.num_args


def num_args(self):
    if self._cache_num_args is None:
        self._cache_num_args = num_args_orig(self)
    return self._cache_num_args


ExprRef.num_args = num_args

ExprRef._is_app = None

orig_is_app = is_app


def is_app(self):
    if self._is_app is None:
        self._is_app = orig_is_app(self)
    return self._is_app


is_app = is_app

ExprRef._cache_kind = None
orig_kind = ExprRef.kind


def expr_kind(self):
    if self._cache_kind is None:
        self._cache_kind = orig_kind(self)
    return self._cache_kind


ExprRef.kind = expr_kind

SortRef._cache_kind = None
orig_sort_kind = SortRef.kind


def sort_kind(self):
    if self._cache_kind is None:
        self._cache_kind = orig_sort_kind(self)
    return self._cache_kind


SortRef.kind = sort_kind

FuncDeclRef._cache_kind = None
orig_func_kind = FuncDeclRef.kind


def func_kind(self):
    if self._cache_kind is None:
        self._cache_kind = orig_func_kind(self)
    return self._cache_kind


FuncDeclRef.kind = func_kind

ExprRef._cache_sort = None
orig_sort = ExprRef.sort


def sort(self):
    if self._cache_sort is None:
        self._cache_sort = orig_sort(self)
    return self._cache_sort


ExprRef.sort = sort

"""
sort_registry is for interning sorts.
Properties can be naturally tagged onto sorts, which can then be looked up by id.
"""

sort_registry: dict[int, SortRef] = {}
_orig_expr_sort = ExprRef.sort


def _expr_sort(self):
    T = _orig_expr_sort(self)
    tid = T.get_id()
    return sort_registry.get(tid, T)


ExprRef.sort = _expr_sort


_IntSort = IntSort
IntS: SortRef = IntSort()
sort_registry[IntS.get_id()] = IntS


def IntSort(ctx=None) -> SortRef:
    if ctx is None:
        return IntS
    else:
        return _IntSort(ctx)


_BoolSort = BoolSort
BoolS: SortRef = BoolSort()
sort_registry[BoolS.get_id()] = BoolS


def BoolSort(ctx=None) -> SortRef:
    if ctx is None:
        return BoolS
    else:
        return _BoolSort(ctx)


_RealSort = RealSort
RealS: SortRef = RealSort()
sort_registry[RealS.get_id()] = RealS


def RealSort(ctx=None) -> SortRef:
    if ctx is None:
        return RealS
    else:
        return _RealSort(ctx)


_DeclareSort = DeclareSort


def DeclareSort(name):
    """
    Declare a sort with the given name.
    >>> DeclareSort("MySort")
    MySort
    """
    T = _DeclareSort(name)
    tid = T.get_id()
    if tid not in sort_registry:
        sort_registry[tid] = T
        return T
    else:
        return sort_registry[tid]


ExprRef.assumes = None
