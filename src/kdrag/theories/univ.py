import kdrag as kd
from kdrag import Inductive, axiom, prove  # noqa: F401
import kdrag.smt as smt
from kdrag.smt import (  # noqa: F401
    ArraySort,
    BoolSort,
    Const,
    DatatypeSort,
    DeclareSort,
    ForAll,
    Function,
    IntSort,
    IntVal,
    Lambda,
    RealSort,
    SeqSort,
)
import functools


"""
A different style using an open datatype instead

https://link.springer.com/chapter/10.1007/978-3-642-12002-2_26  A Polymorphic Intermediate Verification Language: Design and Logical Encoding
"""
Poly = DeclareSort("Poly")


@functools.cache
def _box(s: smt.SortRef) -> smt.FuncDeclRef:
    return Function("box", s, Poly)


def box(term: smt.ExprRef) -> smt.ExprRef:
    return _box(term.sort())(term)


@functools.cache
def _cast(s: smt.SortRef) -> smt.FuncDeclRef:
    return Function(f"cast_{s}", Poly, s)


def cast(s: smt.SortRef, term: smt.ExprRef) -> smt.ExprRef:  # proj
    return _cast(s)(term)


@functools.cache
def poly_ax(s: smt.SortRef) -> kd.Proof:
    """
    >>> prove(cast(IntSort(), box(IntVal(42))) == 42, by=[poly_ax(IntSort())])
    |= cast_Int(box(42)) == 42
    """
    # TODO: is this unsound? It does seem likely this is subject to some kind of vicious circularity
    # assert positive_poly(s)
    x = Const("x", s)
    return axiom(ForAll([x], cast(s, box(x)) == x, patterns=[cast(s, box(x))]))


"""
Specialize some to an inductive datatype so we get built in support for injectors.
"""

Type = Inductive("Type")
_Type = DatatypeSort("Type")
Type.declare("Bool", ("bool", BoolSort()))
Type.declare("Int", ("int", IntSort()))
Type.declare("Real", ("real", RealSort()))
Type.declare("Seq", ("seq", SeqSort(_Type)))
Type.declare("Array", ("array", ArraySort(Poly, _Type)))
# Maybe RFun Real -> Type
# IntFun Int -> Type

Type = Type.create()

# Probably unsound
# type_poly_ax = poly_ax(Type)
_x = Const("x", Type)
Int = Lambda([_x], _x.is_Int)
Real = Lambda([_x], _x.is_Real)
Bool = Lambda([_x], _x.is_Bool)

"""
S = smt.Const("S", smt.SetSort(Type))
mul = smt.Const("mul", smt.ArraySort(Type, Type, Type))
semigroup = kd.define(
    "semigroup", [S, mul], smt.And(kd.Closed(S, mul), kd.Assoc(mul, T=S))
)
"""
