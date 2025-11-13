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


Proof = kernel.Proof


prove = tactics.prove


axiom = kernel.axiom


define = kernel.define

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

# TODO: Remove this
R = smt.RealSort()
Z = smt.IntSort()
RSeq = Z >> R
RFun = R >> R


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
