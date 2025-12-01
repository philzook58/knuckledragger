import kdrag as kd
import kdrag.smt as smt
import functools

_Type0 = kd.Inductive("Type0")
_Type0.declare("Int", ("int", smt.IntSort()))
_Type0.declare("Bool", ("bool", smt.BoolSort()))
_Type0.declare("Real", ("real", smt.RealSort()))
Type0 = _Type0.create()
_x = smt.Const("x", Type0)

Type0Set = smt.FullSet(Type0)
Int0 = smt.Lambda([_x], _x.is_Int)
Bool0 = smt.Lambda([_x], _x.is_Bool)
Real0 = smt.Lambda([_x], _x.is_Real)

"""
Type1 = kd.Inductive("Type1")
Type1.declare("Type0", ("type0", Type0))
Type1.declare("Seq", ("seq", Type1))
Type1Sort = smt.DatatypeSort("Type1")
# We could have deeper recursion at the same universe level
# Type1.declare(
#    "Array", ("array", smt.ArraySort(smt.ArraySort(Type1Sort, Type0), Type1Sort))
# )
Type1.declare("Array", ("array", smt.ArraySort(Type0, Type1Sort)))
Type1 = Type1.create()
"""


def Int(l: int) -> smt.QuantifierRef:
    """
    >>> Int(0)
    Lambda(x, is(Int, x))
    >>> Int(1)
    Lambda(x, And(is(Type0, x), is(Int, type0(x))))
    """
    assert l >= 0
    if l == 0:
        return Int0
    else:
        Typel = Type(l)
        x = smt.Const("x", Typel)
        return smt.Lambda(
            [x], smt.And(Typel.recognizer(0)(x), Int(l - 1)(Typel.accessor(0, 0)(x)))
        )


@functools.cache
def Type(l: int) -> smt.DatatypeSortRef:
    """
    A generic value type at universe level l.
    >>> Type(1)
    Type1
    """
    if l == 0:
        return Type0
    else:
        TypeN = kd.Inductive(f"Type{l}")
        TypeN.declare(f"Type{l - 1}", (f"type{l - 1}", Type(l - 1)))
        TypeNSort = smt.DatatypeSort(f"Type{l}")
        TypeN.declare("Seq", ("seq", smt.SeqSort(TypeNSort)))
        TypeN.declare("Array", ("array", smt.ArraySort(Type(l - 1), TypeNSort)))
        return TypeN.create()
