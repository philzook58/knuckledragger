"""
Knuckledragger is an attempt at creating a down to earth,
highly automated interactive proof assistant in python.
It is not attempting to be the most interesting, expressive,
or flexible logic in the world.

The goal is to support applications like software/hardware verification,
calculus, equational reasoning, and numerical bounds.
"""

from . import smt
from . import kernel
from . import notation
from . import utils
from . import datatype
from . import rewrite
from . import contracts
from . import tactics
from . import reflect
import functools
from .parsers import microlean
import typing


Proof = kernel.Proof


prove = tactics.prove
vprove = tactics.vprove

axiom = kernel.axiom


define = kernel.define


trigger = kernel.trigger


def define_const(name: str, body: smt.ExprRef) -> smt.ExprRef:
    """
    Define a constant.

    >>> x = define_const("define_const_example", smt.IntVal(42))
    >>> x
    define_const_example
    >>> rewrite.unfold(x)
    42
    """
    # TODO: Remove this type ignore and rename all uses of define to define_const where no constants expected
    # arguably define is define_fun
    return kernel.define(name, [], body)  # type: ignore


contract = contracts.contract

FreshVar = kernel.FreshVar

FreshVars = tactics.FreshVars

QImplies = notation.QImplies

QForAll = notation.QForAll

QExists = notation.QExists


cond = notation.cond


Inductive = kernel.Inductive


Struct = datatype.Struct


NewType = datatype.NewType


InductiveRel = datatype.InductiveRel


Enum = datatype.Enum


Calc = tactics.Calc


Lemma = tactics.Lemma
Theorem = tactics.Theorem
PTheorem = tactics.PTheorem

simp = rewrite.simp
full_simp = rewrite.full_simp

search = utils.search

lean = microlean.lean
inductive = microlean.inductive
ldefine = microlean.define

# TODO: Remove this
R = smt.RealSort()
RPosP = smt.Lambda([smt.Real("x")], smt.Real("x") > 0)

Z = smt.IntSort()
RSeq = smt.ArraySort(Z, R)
RFun = smt.ArraySort(R, R)
ZSeq = smt.ArraySort(Z, Z)


IntSet = smt.FullSet(smt.IntSort())
BoolSet = smt.FullSet(smt.BoolSort())
IntP = IntSet
BoolP = BoolSet


def seq(*args):
    """
    Helper to construct sequences.
    >>> seq(1, 2, 3)
    Concat(Unit(1), Concat(Unit(2), Unit(3)))
    >>> seq(1)
    Unit(1)
    """
    if len(args) == 0:
        raise ValueError(
            "seq() requires at least one argument. use smt.Empty(sort) instead."
        )
    elif len(args) == 1:
        return smt.Unit(smt._py2expr(args[0]))
    else:
        return smt.Concat(*[smt.Unit(smt._py2expr(a)) for a in args])


def SeqStore(s: smt.SeqRef, i: smt.ExprRef, v: smt.ExprRef) -> smt.SeqRef:
    """
    >>> _ = prove(SeqStore(seq(1,2,3), 2, 42) == seq(1,2,42))
    >>> _ = prove(SeqStore(seq(1,2,3), 0, 42) == seq(42,2,3))
    """
    i = smt._py2expr(i)
    v = smt._py2expr(v)
    # Check if we've gone off the end?
    return smt.Concat(
        smt.Extract(s, 0, i),
        smt.Unit(v),
        smt.Extract(s, i + 1, smt.Length(s) - (i + 1)),
    )


def Vec(n: smt.ArithRef | int, A: smt.SortRef) -> smt.QuantifierRef:
    l = smt.Const("l", smt.SeqSort(A))
    if isinstance(A, smt.SortRef):
        return smt.Lambda([l], smt.Length(l) == n)
    else:
        # TODO: If A is a subsort
        # x = smt.Const("x", A)
        # return smt.Lambda([l], smt.And(smt.Length(l) == a, smt.ForAll([x], smt.Contains(l,x))))
        raise TypeError("A must be a SortRef")


def Tail(s: smt.SeqSortRef):
    """
    >>> x = smt.Const("x", smt.SeqSort(smt.BoolSort()))
    >>> Tail(x)
    seq.extract(x, 1, Length(x) - 1)
    """
    return smt.SubSeq(s, 1, smt.Length(s) - 1)


def Head(s: smt.SeqRef):
    """
    >>> x = smt.Const("x", smt.SeqSort(smt.BoolSort()))
    >>> Head(x)
    Nth(x, 0)
    >>> prove(smt.Implies(smt.Length(x) > 0, smt.Concat([smt.Unit(Head(x)), Tail(x)]) == x))
    |= Implies(Length(x) > 0,
        Concat(Unit(Nth(x, 0)),
                seq.extract(x, 1, Length(x) - 1)) ==
        x)
    """
    return s[0]


Unit = Inductive("Unit")
Unit.declare("tt")
Unit = Unit.create()


def UnitSort() -> smt.DatatypeSortRef:
    global Unit
    assert isinstance(Unit, smt.DatatypeSortRef)
    return Unit


def Pf(p: smt.BoolRef) -> smt.QuantifierRef:
    """
    >>> Pf(smt.Int("x") > 0)
    Lambda(pf!..., x > 0)
    """
    pf = smt.FreshConst(Unit, prefix="pf")
    return smt.Lambda([pf], p)


_i = smt.Int("i")
NatP = smt.Lambda([_i], _i >= 0)
"""Predicate for natural numbers"""


def FinP(n: smt.ExprRef | int) -> smt.QuantifierRef:
    """
    Predicate for finite index less than n
    >>> FinP(3)
    Lambda(i, And(i >= 0, i < 3))
    >>> x = smt.Const("x", FinP(3)) # Predicate defined constants have predicate auto inserted in quantifiers
    >>> prove(smt.ForAll([x], x < 4))
    |= ForAll(x, Implies(And(x >= 0, x < 3), x < 4))
    """
    i = smt.Int("i")
    return smt.Lambda([i], smt.And(i >= 0, i < n))


Nat = Inductive("Nat")
Nat.declare("Z")
Nat.declare("S", ("pred", Nat))
Nat = Nat.create()


def NatSort() -> smt.DatatypeSortRef:
    global Nat
    assert isinstance(Nat, smt.DatatypeSortRef)
    return Nat


@functools.cache
def ListSort(Elt: smt.SortRef) -> smt.DatatypeSortRef:
    """
    >>> ListSort(smt.IntSort())
    List_Int...
    """
    T = Inductive("List_" + Elt.name())
    T.declare("Nil")
    T.declare("Cons", ("head", Elt), ("tail", T))
    return T.create()


def list(*args: smt.ExprRef) -> smt.DatatypeRef:
    """
    Helper to construct List values
    >>> list(1, 2, 3)
    Cons(1, Cons(2, Cons(3, Nil)))
    """
    if len(args) == 0:
        raise ValueError("list() requires at least one argument")
    LT = ListSort(smt._py2expr(args[0]).sort())
    acc = LT.Nil
    for a in reversed(args):
        acc = LT.Cons(a, acc)
    return acc


@functools.cache
def OptionSort(T: smt.SortRef) -> smt.DatatypeSortRef:
    """
    Define an Option type for a given type T
    >>> OInt = OptionSort(smt.IntSort())
    >>> OInt.Some(1)
    Some(1)
    >>> OInt.None_
    None_
    >>> OInt.Some(1).val
    val(Some(1))
    """
    Option = Inductive("Option_" + T.name())
    Option.declare("None_")
    Option.declare("Some", ("val", T))
    return Option.create()


# I guess I could make this a SortDispatch for regularity. I just don't see why I'd need to overload in any way but the default
def Some(x: smt.ExprRef) -> smt.DatatypeRef:
    """
    Helper to create Option values
    >>> Some(42)
    Some(42)
    >>> Some(42).sort()
    Option_Int
    """
    x = smt._py2expr(x)
    return OptionSort(x.sort()).Some(x)


@functools.cache
def TupleSort(*elts: smt.SortRef) -> smt.DatatypeSortRef:
    """
    Define a Tuple type for given element types
    >>> T = TupleSort(smt.IntSort(), smt.BoolSort())
    >>> t = T(42, True)
    >>> t
    Tuple_Int_Bool(42, True)
    >>> t._0
    _0(Tuple_Int_Bool(42, True))
    >>> t._1
    _1(Tuple_Int_Bool(42, True))
    """
    name = "Tuple_" + "_".join(e.name() for e in elts)
    Tuple = Inductive(name)
    Tuple.declare(name, *[(f"_{i}", elt) for i, elt in enumerate(elts)])
    return Tuple.create()


def tuple_(*args: smt.ExprRef) -> smt.DatatypeRef:
    """
    Helper to create Tuple values
    >>> t = tuple_(42, True)
    >>> t
    Tuple_Int_Bool(42, True)
    >>> t.sort()
    Tuple_Int_Bool
    """
    # debatably this should take in a iterator like built in python `tuple`
    args1 = [smt._py2expr(a) for a in args]
    T = TupleSort(*(a.sort() for a in args1))
    return T(*args1)


def is_tuple_sort(s: smt.SortRef) -> bool:
    return isinstance(s, smt.DatatypeSortRef) and s.name().startswith("Tuple_")


def is_tuple(e: smt.ExprRef) -> bool:
    sort = e.sort()
    return isinstance(sort, smt.DatatypeSortRef) and is_tuple_sort(sort)


Complex = datatype.Struct("C", ("re", smt.RealSort()), ("im", smt.RealSort()))
ComplexP = smt.FullSet(Complex)


def is_complex(e: smt.ExprRef) -> bool:
    return e.sort() == Complex


z, w, u, z1, z2 = smt.Consts("z w u z1 z2", Complex)
complex_add = notation.add.define([z1, z2], Complex.C(z1.re + z2.re, z1.im + z2.im))
complex_mul = notation.mul.define(
    [z1, z2], Complex.C(z1.re * z2.re - z1.im * z2.im, z1.re * z2.im + z1.im * z2.re)
)
complex_div = notation.div.define(
    [z1, z2],
    Complex.C(
        (z1.re * z2.re + z1.im * z2.im) / (z2.re**2 + z2.im**2),
        (z1.im * z2.re - z1.re * z2.im) / (z2.re**2 + z2.im**2),
    ),
)
J = Complex.C(0, 1)
complex_one = Complex.C(1, 0)


def ComplexSort() -> smt.DatatypeSortRef:
    """
    >>> C = ComplexSort()
    >>> z, w = smt.Consts("z w", C)
    >>> full_simp(J + J)
    C(0, 2)
    >>> full_simp(J * J)
    C(-1, 0)
    >>> full_simp(J / J)
    C(1, 0)
    """
    return Complex


def Id(T: smt.SortRef) -> smt.QuantifierRef:
    """
    >>> Id(smt.IntSort())
    Lambda(x, x)
    """
    x = smt.Const("x", T)
    return smt.Lambda([x], x)


def Undef(sort: smt.SortRef, *args) -> smt.ExprRef:
    """
    Create an "undefined" value possibly dependent on other values.
    You will not be able to prove anything about this value that is not true of any symbol.

    >>> Undef(smt.IntSort())
    undef!...
    >>> x = smt.Const("x", smt.IntSort())
    >>> Undef(smt.IntSort(), x)
    f!...(x)
    """
    if len(args) == 0:
        return smt.FreshConst(sort, prefix="undef")
    else:
        return smt.FreshFunction(*[arg.sort() for arg in args], sort)(*args)


@functools.cache
def guard(T: smt.SortRef):
    T.name()
    cond = smt.Bool("cond")
    x = smt.Const("x", T)
    return define(T.name() + ".guard", [cond, x], smt.If(cond, x, Undef(T, x)))


def Guard(cond: smt.BoolRef, body: smt.ExprRef) -> smt.ExprRef:
    """
    Make a guard over an expression.
    If the condition is true, this is just the expression.
    If the condition is false, this is an unconstrained value of the same sort as the expression.

    >>> x = smt.Real("x")
    >>> Guard(x >= 0, smt.Sqrt(x))
    Real.guard(x >= 0, x**(1/2))
    """
    return guard(body.sort())(cond, body)


def _infer_sort(
    F: smt.FuncRef, sort: typing.Optional[smt.ArraySortRef]
) -> smt.ArraySortRef:
    if sort is not None:
        return sort
    elif smt.is_func(F):
        S = smt.domains(F)[0]
        assert (
            isinstance(S, smt.ArraySortRef) and S.range() == smt.BoolSort()
        ), "sort must be Set(T) for some T"
        return S
    else:
        raise ValueError("sort must be provided for non-function F")


def SetMonotone(F, sort=None):
    """
    >>> ZSet = smt.SetSort(smt.IntSort())
    >>> F = smt.Array("F", ZSet, ZSet)
    >>> SetMonotone(F)
    ForAll([A!..., B!...], Implies(subset(A!..., B!...), subset(F[A!...], F[B!...])))
    """

    SetSort = _infer_sort(F, sort)
    A = smt.FreshConst(SetSort, prefix="A")
    B = smt.FreshConst(SetSort, prefix="B")
    return smt.ForAll([A, B], A <= B, F(A) <= F(B))


def PreFix(F, A):
    return F(A) <= A


def PostFix(F, A):
    return A <= F(A)


def LFP(F, sort=None):
    """
    >>> ZSet = smt.SetSort(smt.IntSort())
    >>> F = smt.Array("F", ZSet, ZSet)
    >>> LFP(F)
    Lambda(x!...,
        ForAll(A!...,
                Implies(subset(F[A!...], A!...), A!...[x!...])))
    """
    SetSort = _infer_sort(F, sort)
    x = smt.FreshConst(SetSort.domain(), prefix="x")
    A = smt.FreshConst(SetSort, prefix="A")
    return smt.Lambda([x], smt.ForAll([A], PreFix(F, A), A[x]))


def GFP(F, sort=None):
    """
    >>> ZSet = smt.SetSort(smt.IntSort())
    >>> F = smt.Array("F", ZSet, ZSet)
    >>> GFP(F)
    Lambda(x!...,
        Exists(A!...,
                And(subset(A!..., F[A!...]), A!...[x!...])))
    """
    SetSort = _infer_sort(F, sort)
    x = smt.FreshConst(SetSort.domain(), prefix="x")
    A = smt.FreshConst(SetSort, prefix="A")
    return smt.Lambda([x], smt.Exists([A], PostFix(F, A), A[x]))


@functools.cache
def trans(step: smt.FuncDeclRef) -> smt.FuncDeclRef:
    """
    The transitive closure of a step function. Takes a function of type `State -> State`
    and returns a function of type `Int, State -> State` where the first argument is the number of steps to take.

    >>> hr = smt.Int("hr")
    >>> clk_step = define("clk_step", [hr], smt.If(hr == 12, 1, hr + 1))
    >>> clk_trans = trans(clk_step)
    >>> full_simp(clk_trans(4, 1))
    5
    >>> full_simp(clk_trans(12, 1))
    1
    >>> full_simp(clk_trans(-3, 42)) # stutters on negative steps
    42
    """
    name = "trans_" + step.name()
    n = smt.Int("n")
    State = step.range()
    st = smt.Const("st", State)
    trans = smt.Function(name, smt.IntSort(), State, State)
    return define(
        "trans_" + step.name(), [n, st], smt.If(n <= 0, st, step(trans(n - 1, st)))
    )


def MetaVar(name: str, sort: smt.SortRef) -> smt.ExprRef:
    """
    A metavariable is just a regular smt constant whose names starts with "?".
    It is not used in the kernel, but certain utility functions may use this property to try
    and find a replacement for the metavariable.

    >>> foo = MetaVar("foo", smt.IntSort())
    >>> foo
    ?foo
    >>> smt.is_const(foo)
    True
    """
    return smt.Const("?" + name, sort)


def is_metavar(c: smt.ExprRef) -> bool:
    """
    >>> assert is_metavar(MetaVar("foo", smt.IntSort()))
    """
    return smt.is_const(c) and c.decl().name().startswith("?")


symdef = reflect.reflect
struct = reflect.struct
# Shortenings
Expr = smt.ExprRef
Sort = smt.SortRef
Decl = smt.FuncDeclRef

add = notation.add
sub = notation.sub
mul = notation.mul
div = notation.div
le = notation.le
lt = notation.lt
ge = notation.ge
gt = notation.gt
eq = notation.eq
ne = notation.ne
and_ = notation.and_
or_ = notation.or_
invert = notation.invert


__all__ = [
    "prove",
    "axiom",
    "define",
    "Proof",
    "FreshVar",
    "FreshVars",
    "QImplies",
    "QForAll",
    "QExists",
    "cond",
    "Struct",
    "NewType",
    "Inductive",
    "Calc",
    "Lemma",
    "Theorem",
    "PTheorem",
    "R",
    "Z",
    "RSeq",
    "RFun",
    "simp",
    "search",
]
