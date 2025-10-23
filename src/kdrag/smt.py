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


def ForAll(vs: list[ExprRef], *hyp_conc, **kwargs) -> QuantifierRef:
    """
    Quantified ForAll

    Shorthand for `ForAll(vars, Implies(And(hyp[0], hyp[1], ...), conc))`

    >>> x,y = Ints("x y")
    >>> ForAll([x,y], x > 0, y > 0, x + y > 0)
    ForAll([x, y], Implies(And(x > 0, y > 0), x + y > 0))
    >>> x = Const("x", Lambda([x], x >= 0))
    >>> ForAll([x], x > 3)
    ForAll(x, Implies(x >= 0, x > 3))

    """
    if any(v.assumes is not None for v in vs):
        # fast path avoids this
        hyp_conc0 = hyp_conc
        hyp_conc = [v.assumes for v in vs if v.assumes is not None]
        hyp_conc.extend(hyp_conc0)
    l = len(hyp_conc)
    assert l > 0
    if l == 1:
        return RawForAll(vs, hyp_conc[0], **kwargs)
    elif l == 2:
        return RawForAll(vs, Implies(hyp_conc[0], hyp_conc[1]), **kwargs)
    else:
        return RawForAll(vs, Implies(And(hyp_conc[:-1]), hyp_conc[-1]), **kwargs)


def Exists(vs: list[ExprRef], *concs, **kwargs) -> QuantifierRef:
    """
    Quantified Exists

    Shorthand for `Exists(vars, And(conc[0], conc[1], ...))`

    >>> x,y = Ints("x y")
    >>> Exists([x,y], x > 0, y > 0)
    Exists([x, y], And(x > 0, y > 0))
    >>> x = Const("x", Lambda([x], x >= 0))
    >>> Exists([x], x > 3)
    Exists(x, And(x >= 0, x > 3))
    """
    if any(v.assumes is not None for v in vs):
        # fast path avoids this
        concs0 = concs
        concs = [v.assumes for v in vs if v.assumes is not None]
        concs.extend(concs0)
    if len(concs) == 1:
        return RawExists(vs, concs[0], **kwargs)
    else:
        return RawExists(vs, And(concs), **kwargs)


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


type FuncRef = ArrayRef | QuantifierRef


def is_func(f: ExprRef) -> bool:
    """
    Check if a term is a function or an array.

    >>> x = Int("x")
    >>> assert is_func(Lambda([x], x))
    """
    return is_array(f) or (isinstance(f, QuantifierRef) and f.is_lambda())


def domains(f: FuncRef | ArraySortRef) -> list[SortRef]:
    """
    Get the domain sorts of a lambda or an array.

    >>> x = Int("x")
    >>> y = Real("y")
    >>> f = Array("f", IntSort(), RealSort(), IntSort())
    >>> domains(f)
    [Int, Real]
    >>> lam = Lambda([x, y], x + y)
    >>> domains(lam)
    [Int, Real]
    """
    if isinstance(f, ArrayRef) or isinstance(f, ArraySortRef):
        res = []
        i = 0
        try:  # I do not know a better way than to try and catch to determine arity of array
            while True:
                res.append(f.domain_n(i))
                i += 1
        except Z3Exception:
            return res
    elif isinstance(f, QuantifierRef) and f.is_lambda():
        return [f.var_sort(i) for i in range(f.num_vars())]
    else:
        raise TypeError(f"Expected ArrayRef or Lambda, got {f}")


def codomain(f: FuncRef | ArraySortRef) -> SortRef:
    """
    >>> x = Int("x")
    >>> y = Int("y")
    >>> f = Array("f", IntSort(), RealSort())
    >>> codomain(f)
    Real
    >>> lam = Lambda([x, y], x + y)
    >>> codomain(lam)
    Int

    """
    if isinstance(f, ArrayRef) or isinstance(f, ArraySortRef):
        return f.range()
    elif isinstance(f, QuantifierRef) and f.is_lambda():
        return f.body().sort()
    else:
        raise TypeError(f"Expected ArrayRef or Lambda, got {f}")


RawConst = Const


def Const(name: str, sort: SortRef | FuncRef) -> ExprRef:
    """
    Create a constant of a given sort.
    If a set value is given as the sort, this is treated as a constraint
    held in the `assumes` field of the constant.
    This field may be used by quantifiers.

    >>> n = Int("n")
    >>> x = Const("x", Lambda([n], n >= 0))
    >>> x.assumes
    x >= 0
    """
    if isinstance(sort, SortRef):
        return RawConst(name, sort)
    else:
        doms = domains(sort)
        assert len(doms) == 1 and codomain(sort) == BoolSort()
        x = RawConst(name, doms[0])
        x.assumes = sort(x)
        return x


RawConsts = Consts


def Consts(names: str, sort: SortRef | FuncRef) -> list[ExprRef]:
    """
    >>> n = Int("n")
    >>> xs = Consts("x y z", Lambda([n], n >= 0))
    >>> [x.assumes for x in xs]
    [x >= 0, y >= 0, z >= 0]
    """
    if isinstance(sort, SortRef):
        return RawConsts(names, sort)
    else:
        doms = domains(sort)
        assert len(doms) == 1 and codomain(sort) == BoolSort()
        xs = RawConsts(names, doms[0])
        for x in xs:
            x.assumes = sort(x)
        return xs
