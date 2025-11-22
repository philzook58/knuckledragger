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
from . import tactics
import functools
from .parsers import microlean


Proof = kernel.Proof


prove = tactics.prove


axiom = kernel.axiom


define = kernel.define


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

search = utils.search

expr = microlean.parse

# TODO: Remove this
R = smt.RealSort()
Z = smt.IntSort()
RSeq = Z >> R
RFun = R >> R

Int = smt.FullSet(smt.IntSort())
Bool = smt.FullSet(smt.BoolSort())


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


Unit = Inductive("Unit")
Unit.declare("tt")
Unit = Unit.create()


def UnitSort() -> smt.DatatypeSortRef:
    global Unit
    assert isinstance(Unit, smt.DatatypeSortRef)
    return Unit


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


def Assoc(f) -> smt.BoolRef:
    """
    >>> Assoc(smt.Function("f", smt.IntSort(), smt.IntSort(), smt.IntSort()))
    ForAll([x, y, z], f(f(x, y), z) == f(x, f(y, z)))
    """
    T = f.range()
    x, y, z = smt.Consts("x y z", T)
    return smt.ForAll([x, y, z], f(f(x, y), z) == f(x, f(y, z)))


def Comm(f) -> smt.BoolRef:
    """
    >>> Comm(smt.Function("f", smt.IntSort(), smt.IntSort(), smt.IntSort()))
    ForAll([x, y], f(x, y) == f(y, x))
    """
    T = f.range()
    x, y = smt.Consts("x y", T)
    return smt.ForAll([x, y], f(x, y) == f(y, x))


def Idem(f) -> smt.BoolRef:
    """
    >>> Idem(smt.Function("f", smt.IntSort(), smt.IntSort(), smt.IntSort()))
    ForAll(x, f(x, x) == x)
    """
    T = f.range()
    x = smt.Const("x", T)
    return smt.ForAll([x], f(x, x) == x)


def LeftIdentity(f, e: smt.ExprRef) -> smt.BoolRef:
    """
    >>> LeftIdentity(smt.Function("f", smt.IntSort(), smt.IntSort(), smt.IntSort()), smt.IntVal(0))
    ForAll(x, f(0, x) == x)
    """
    T = f.range()
    x = smt.Const("x", T)
    return smt.ForAll([x], f(e, x) == x)


def RightIdentity(f, e: smt.ExprRef) -> smt.BoolRef:
    """
    >>> RightIdentity(smt.Function("f", smt.IntSort(), smt.IntSort(), smt.IntSort()), smt.IntVal(0))
    ForAll(x, f(x, 0) == x)
    """
    T = f.range()
    x = smt.Const("x", T)
    return smt.ForAll([x], f(x, e) == x)


def SemiGroup(f) -> smt.BoolRef:
    return Assoc(f)


def AbelSemiGroup(f) -> smt.BoolRef:
    return smt.And(SemiGroup(f), Comm(f))


def Monoid(f, e: smt.ExprRef) -> smt.BoolRef:
    return smt.And(SemiGroup(f), LeftIdentity(f, e), RightIdentity(f, e))


def CommMonoid(f, e: smt.ExprRef) -> smt.BoolRef:
    return smt.And(AbelSemiGroup(f), LeftIdentity(f, e))


def SemiRing(add, mul, zero, one) -> smt.BoolRef:
    T = zero.sort()
    x, y, z = smt.Consts("x y z", T)
    return smt.And(
        CommMonoid(add, zero),
        Monoid(mul, one),
        smt.ForAll([x], mul(x, zero) == zero),
        smt.ForAll([x], mul(zero, x) == zero),
        smt.ForAll([x, y, z], mul(x, add(y, z)) == add(mul(x, y), mul(x, z))),
        smt.ForAll([x, y, z], mul(add(x, y), z) == add(mul(x, z), mul(y, z))),
    )


def CommSemiRing(add, mul, zero, one) -> smt.BoolRef:
    return smt.And(
        SemiRing(add, mul, zero, one),
        Comm(mul),
    )


def Refl(rel) -> smt.BoolRef:
    """
    >>> Refl(smt.Function("rel", smt.IntSort(), smt.IntSort(), smt.BoolSort()))
    ForAll(x, rel(x, x))
    """
    T = rel.domain(0)
    x = smt.Const("x", T)
    return smt.ForAll([x], rel(x, x))


def Antisymm(rel) -> smt.BoolRef:
    """
    >>> Antisymm(smt.Function("rel", smt.IntSort(), smt.IntSort(), smt.BoolSort()))
    ForAll([x, y], Implies(And(rel(x, y), rel(y, x)), x == y))
    """
    T = rel.domain(0)
    x, y = smt.Consts("x y", T)
    return smt.ForAll([x, y], smt.Implies(smt.And(rel(x, y), rel(y, x)), x == y))


def Id(T: smt.SortRef) -> smt.QuantifierRef:
    """
    >>> Id(smt.IntSort())
    Lambda(x, x)
    """
    x = smt.Const("x", T)
    return smt.Lambda([x], x)


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
