"""
Symbolic union a la Rosette

"""

from dataclasses import dataclass
import kdrag.smt as smt
from typing import Callable, Optional
import operator
from functools import singledispatch
import kdrag as kd


@dataclass(frozen=True)
class SymUnion[T]:
    """
    Symbolic Union. A SymUnion[T] represents a value of type T that can be one of several possibilities,
    each with an associated symbolic boolean condition.

    https://docs.racket-lang.org/rosette-guide/sec_value-reflection.html
    https://hackage.haskell.org/package/grisette

    >>> su1 = SymUnion.wrap(42)

    """

    values: tuple[tuple[smt.BoolRef, T], ...]

    @classmethod
    def of_list(cls, values: list[tuple[smt.BoolRef, T]]) -> "SymUnion[T]":
        """
        Create a SymUnion from a list of (condition, value) pairs.

        >>> su2 = SymUnion.of_list([(smt.BoolVal(True), 42), (smt.BoolVal(False), 43)])
        >>> su2
        SymUnion(values=((True, 42), (False, 43)))
        """
        # TODO: check keyword?
        return cls(tuple(values))

    @classmethod
    def wrap(cls, v: T, ctx=smt.BoolVal(True)) -> "SymUnion[T]":
        """
        Wrap a value in a SymUnion. This is monadic pure/return
        >>> SymUnion.wrap(42)
        SymUnion(values=((True, 42),))
        """
        return cls(((ctx, v),))

    @classmethod
    def empty(cls) -> "SymUnion[T]":
        """
        The empty SymUnion. This is the identity for union and the annihilator for intersection.
        >>> SymUnion.empty()
        SymUnion(values=())
        """
        return cls(())

    # Is this useful? Why wouldn't you just call FreshBool? It's kind of interesting for roulette
    @staticmethod
    def flip() -> "SymUnion[bool]":
        """
        Flip a coin.

        >>> SymUnion.flip()
        SymUnion(values=((b!..., True), (Not(b!...), False)))
        """
        v = smt.FreshBool()
        return SymUnion.of_list([(v, True), (smt.Not(v), False)])

    def valueize(self: "SymUnion[smt.ExprRef]") -> "SymUnion[smt.ExprRef]":
        """
        Use smt solver to enumrate all possible models of the expression.
        """
        # TODO: Could add a optional keyword arg limit. Leave last one symbolic.
        values = []
        for ctx, expr in self.values:
            s = smt.Solver()
            if ctx is not None:
                s.add(ctx)
            v = smt.FreshConst(expr.sort())
            s.add(v == expr)
            while True:
                res = s.check()
                if res == smt.sat:
                    m = s.model()
                    val = m.eval(v, model_completion=True)
                    if ctx is not None:
                        cond = smt.And(ctx, expr == val)
                    else:
                        cond = expr == val
                    values.append((cond, expr2py(val)))
                    s.add(expr != val)
                elif res == smt.unsat:
                    break
                else:
                    raise ValueError("Solver returned unknown", expr)
        return SymUnion.of_list(values)

    def concretize(self: "SymUnion[smt.ExprRef]") -> "SymUnion[object]":
        """
        Turn a symbolic expression into all combinations of
        """
        return self.valueize().map(expr2py)

    def assume(self: "SymUnion[T]", cond: smt.BoolRef) -> "SymUnion[T]":
        """
        Add a guard to the SymUnion.
        The could also be called guard or project or perhaps filter.
        """
        # guard
        # TODO, hmm. Actually, the cond could optionally take in the value. Would that be useful?
        # Or cond could be a SymUnion
        return SymUnion.of_list([smt.And(cond, cond1) for cond1, v in self.values])

    def collect(self: "SymUnion[smt.ExprRef]") -> "SymUnion[smt.ExprRef]":
        """
        Collect via if-then-else chain all the branches into a single guarded expression.
        This is a merge of symbolic states into a single symbolic state.
        It internalizes the branching back into the solver

        >>> b = smt.Bool("b")
        >>> su = SymUnion.of_list([(b, 42), (smt.Not(b), 43)]).map(py2expr)
        >>> su.collect()
        SymUnion(values=((Or(b, Not(b)), If(b, 42, If(Not(b), 43, undef!...))),))
        """
        # collect into partial expressoin PartialExpr?
        if len(self.values) == 0:
            return SymUnion.empty()
        else:
            v = self.values[0][1]
            if not isinstance(v, smt.ExprRef):
                raise ValueError(
                    "collect only works on SymUnion of ExprRefs",
                    self,
                    "try x.map(pyexpr).collect()",
                )
            sort = v.sort()
        acc_expr = kd.Undef(sort)
        for cond, expr in reversed(self.values):
            acc_expr = smt.If(cond, expr, acc_expr)
        ctx = smt.Or([cond for cond, _ in self.values])
        return SymUnion.wrap(acc_expr, ctx=ctx)

    def prune(self: "SymUnion[T]") -> "SymUnion[T]":
        """
        Remove impossible conditions via smt query.

        >>> su = SymUnion.of_list([(smt.BoolVal(True), 42), (smt.BoolVal(False), 43)])
        >>> su.prune()
        SymUnion(values=((True, 42),))
        """
        new_values = []
        for cond1, v1 in self.values:
            s = smt.Solver()
            s.add(cond1)
            res = s.check()
            if res == smt.sat:
                new_values.append((cond1, v1))
            elif res == smt.unsat:
                pass
            else:
                raise ValueError("Solver returned unknown", cond1)
        return SymUnion.of_list(new_values)

    def map[U](self: "SymUnion[T]", f: Callable[[T], U]) -> "SymUnion[U]":
        return SymUnion.of_list([(k, f(v)) for k, v in self.values])

    def map2[U, V](
        self: "SymUnion[T]", other: "SymUnion[U]", f: Callable[[T, U], V]
    ) -> "SymUnion[V]":
        """
        Map a binary function over two SymUnions

        """
        new_values = []
        for cond1, v1 in self.values:
            # if cond1 in other.values: ? avoid loop join?
            for cond2, v2 in other.values:
                new_values.append((smt.And(cond1, cond2), f(v1, v2)))
        return SymUnion.of_list(new_values)

    def flatmap[U](
        self: "SymUnion[T]", f: Callable[[T], "SymUnion[U]"], strict=False
    ) -> "SymUnion[U]":
        new_values = []
        for cond1, v1 in self.values:
            su2 = f(v1)
            if isinstance(su2, SymUnion):
                for cond2, v2 in su2.values:
                    new_values.append((smt.And(cond1, cond2), v2))
            else:  # act like map if f doesn't return a SymUnion. Could instead fail
                if strict:
                    raise ValueError("Expected f to return a SymUnion", v1, su2)
                new_values.append((cond1, su2))
        return SymUnion.of_list(new_values)

    def join(self: "SymUnion[SymUnion[T]]") -> "SymUnion[T]":
        """
        Flatten a SymUnion of SymUnions. This is monadic join
        """
        new_values = []
        for cond1, su2 in self.values:
            for cond2, v2 in su2.values:
                new_values.append((smt.And(cond1, cond2), v2))
        return SymUnion.of_list(new_values)

    # operator overloads
    # https://docs.python.org/3/library/operator.html

    def __lt__(self: "SymUnion", other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.lt)

    def __le__(self: "SymUnion", other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.le)

    def __eq__(self, other: "SymUnion") -> "SymUnion":  # type: ignore
        return self.map2(other, operator.eq)

    def __ne__(self: "SymUnion", other: "SymUnion") -> "SymUnion":  # type: ignore
        return self.map2(other, operator.ne)

    def __ge__(self: "SymUnion", other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.ge)

    def __add__(self, other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.add)

    def __and__(self, other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.and_)

    def __not__(self: "SymUnion") -> "SymUnion":
        return self.map(operator.not_)

    def __invert__(self: "SymUnion") -> "SymUnion":
        return self.map(operator.invert)

    def __lshift__(self: "SymUnion", other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.lshift)

    def __mul__(self, other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.mul)

    def __matmul__(self, other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.matmul)

    def __neg__(self: "SymUnion") -> "SymUnion":
        return self.map(operator.neg)

    def __or__(self, other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.or_)

    def __pow__(self: "SymUnion", other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.pow)

    def __rshift__(self: "SymUnion", other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.rshift)

    def __sub__(self, other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.sub)

    def __truediv__(self: "SymUnion", other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.truediv)

    def __xor__(self: "SymUnion", other: "SymUnion") -> "SymUnion":
        return self.map2(other, operator.xor)

    def __getitem__(self: "SymUnion", key: "SymUnion") -> "SymUnion":
        return self.map2(key, operator.getitem)

    def __len__(self: "SymUnion") -> "SymUnion":
        return self.map(len)

    def __getattr__(self: "SymUnion", name: str) -> "SymUnion":
        # if name is _also_ a SymUnion, you are insane.
        return self.map(lambda v: getattr(v, name))

    def store(self: "SymUnion[tuple]", index: int, value: "SymUnion") -> "SymUnion":
        # TODO: index could also be symbolic.
        def _store(t, v):
            x = list(t)
            x[index] = v
            return tuple(x)

        return self.map2(value, _store)

    def _replace(self: "SymUnion", **kwargs) -> "SymUnion":
        # like dataclass replace but for SymUnion. Only works if the values are dataclasses. Could be useful for symbolic states.
        assert len(kwargs) == 1, "Only support replacing one field at a time for now"
        ((k, v),) = kwargs.items()
        return self.map2(v, lambda a, b: a._replace(k=b))


# should this go in reflect?
@singledispatch
def py2expr(x: object) -> smt.ExprRef:
    """
    >>> py2expr(1)
    1
    >>> py2expr(1.5)
    3/2
    >>> py2expr(True)
    True
    >>> py2expr("hello")
    "hello"
    >>> py2expr((1, 2))
    Tuple_Int_Int(1, 2)
    >>> py2expr({1, 2})
    Store(Store(K(Int, False), 1, True), 2, True)
    >>> py2expr([1,2,4,6])
    Concat(Unit(1), Concat(Unit(2), Concat(Unit(4), Unit(6))))
    >>> py2expr(1+2j)
    C(1, 2)
    """
    return smt._py2expr(x)


# Or should it quote? Kind of interesting.
@py2expr.register
def _(x: smt.ExprRef) -> smt.ExprRef:
    return x


# values only?
# cvc5.ExprRef -> z3.ExprRef?
# sympy.Expr -> z3.ExprRef?


@py2expr.register
def _(x: int) -> smt.ExprRef:
    return smt.IntVal(x)


@py2expr.register
def _(x: float) -> smt.ExprRef:
    return smt.RealVal(x)


@py2expr.register
def _(x: bool) -> smt.ExprRef:
    return smt.BoolVal(x)


@py2expr.register
def _(x: str) -> smt.ExprRef:
    return smt.StringVal(x)


@py2expr.register
def _(x: tuple) -> smt.ExprRef:
    return kd.tuple_(*[py2expr(e) for e in x])


@py2expr.register
def _(x: list) -> smt.ExprRef:
    return kd.seq(*[py2expr(e) for e in x])


@py2expr.register
def _(x: complex) -> smt.ExprRef:
    return kd.Complex.C(x.real, x.imag)


@py2expr.register
def _(x: set) -> smt.ExprRef:
    if not x:
        raise ValueError("Can't infer z3 sort of empty set")
    xs = [py2expr(e) for e in list(x)]
    s = xs[0].sort()
    acc = smt.EmptySet(s)
    for a in xs:
        acc = smt.SetAdd(acc, a)
    return acc


@py2expr.register
def _(x: frozenset) -> smt.ExprRef:
    return py2expr(set(x))


# @py2expr.register
# def _(x: SymUnion) -> smt.ExprRef:
# if then else with kd.Undef()?


def expr2py_default(e: smt.ExprRef) -> object:
    if isinstance(e, smt.IntNumRef):
        return e.as_long()
    elif isinstance(e, smt.RatNumRef):
        return e.as_fraction()
    elif isinstance(e, smt.BitVecNumRef):
        return e.as_long()
    elif isinstance(e, smt.BoolRef) and smt.is_true(e):
        return True
    elif isinstance(e, smt.BoolRef) and smt.is_false(e):
        return False
    elif (
        isinstance(e, smt.DatatypeRef)
        and smt.is_constructor(e)
        and e.sort().num_constructors() == 1
    ):
        return tuple(expr2py(e.accessor_value(i)) for i in range(e.num_args()))
    # if is_tuple(e): return tuple
    # if is_datatype and is_constructor: return {accessor : expr2py(accessor(e)) for accessor in accessors}
    # elif isinstance(e, smt.SeqRef) and smt.is_unit(e):
    #    return [expr2py(e.arg(0))]
    # elif isinstance(e, smt.SeqRef) and smt.is_concat(e):
    #    return sum([expr2py(c) for c in e.children()])
    # elif isinstance(e, smt.SetRef) and smt.is_empty_set(e):
    else:
        return e  # return None  # Hmm. But maybe we want to return None for Option


expr2py = kd.notation.SortDispatch(default=expr2py_default)

"""
class SymPartial[T] 
A single entry of symunion. The Maybe monand to it's List. But why bother?
"""


@dataclass(frozen=True)
class PartialExpr:
    expr: smt.ExprRef
    cond: Optional[smt.BoolRef] = None

    def __getattr__(self, name):
        return getattr(self.expr, name)

    def map(self, f: Callable[[smt.ExprRef], smt.ExprRef]) -> "PartialExpr":
        return PartialExpr(f(self.expr), self.cond)

    def map2(
        self, other: "PartialExpr", f: Callable[[smt.ExprRef, smt.ExprRef], smt.ExprRef]
    ) -> "PartialExpr":
        if self.cond is not None and other.cond is not None:
            cond = smt.And(self.cond, other.cond)
        elif self.cond is not None:
            cond = self.cond
        elif other.cond is not None:
            cond = other.cond
        else:
            cond = None
        return PartialExpr(f(self.expr, other.expr), cond)


@dataclass(frozen=True)
class PartialFuncDecl:
    decl: smt.FuncDeclRef
    contract: Optional[Callable[[smt.ExprRef], smt.BoolRef]] = None

    def __call__(self, *args):
        if self.contract is not None:
            cond = self.contract(*args)
            return PartialExpr(self.decl(*args), cond)
        else:
            return PartialExpr(self.decl(*args))
