import kdrag as kd
import kdrag.smt as smt
import functools


"""
A different style using an open datatype instead

https://link.springer.com/chapter/10.1007/978-3-642-12002-2_26  A Polymorphic Intermediate Verification Language: Design and Logical Encoding
"""
Poly = smt.DeclareSort("Poly")


@functools.cache
def _box(s: smt.SortRef) -> smt.FuncDeclRef:
    return smt.Function("box", s, Poly)


def box(term: smt.ExprRef) -> smt.ExprRef:
    return _box(term.sort())(term)


@functools.cache
def _cast(s: smt.SortRef) -> smt.FuncDeclRef:
    return smt.Function(f"cast_{s}", Poly, s)


def cast(s: smt.SortRef, term: smt.ExprRef) -> smt.ExprRef:  # proj
    return _cast(s)(term)


@functools.cache
def poly_ax(s: smt.SortRef) -> kd.Proof:
    """
    >>> kd.prove(cast(smt.IntSort(), box(smt.IntVal(42))) == 42, by=[poly_ax(smt.IntSort())])
    |= cast_Int(box(42)) == 42
    """
    # TODO: is this unsound? It does seem likely this is subject to some kind of vicious circularity
    # assert positive_poly(s)
    x = smt.Const("x", s)
    return kd.axiom(smt.ForAll([x], cast(s, box(x)) == x, patterns=[cast(s, box(x))]))


"""
Specialize some to an inductive datatype so we get built in support for injectors.
"""

Type = kd.Inductive("Type")
_Type = smt.DatatypeSort("Type")
Type.declare("Bool", ("bool", smt.BoolSort()))
Type.declare("Int", ("int", smt.IntSort()))
Type.declare("Real", ("real", smt.RealSort()))
Type.declare("Seq", ("seq", smt.SeqSort(_Type)))
Type.declare("Array", ("array", smt.ArraySort(Poly, _Type)))
# Maybe RFun Real -> Type
# IntFun Int -> Type

Type = Type.create()

# Probably unsound
# type_poly_ax = poly_ax(Type)
_x = smt.Const("x", Type)
Int = smt.Lambda([_x], _x.is_Int)
Real = smt.Lambda([_x], _x.is_Real)
Bool = smt.Lambda([_x], _x.is_Bool)

"""
S = smt.Const("S", smt.SetSort(Type))
mul = smt.Const("mul", smt.ArraySort(Type, Type, Type))
semigroup = kd.define(
    "semigroup", [S, mul], smt.And(kd.Closed(S, mul), kd.Assoc(mul, T=S))
)
"""
