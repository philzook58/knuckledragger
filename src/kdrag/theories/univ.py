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
Nat0 = smt.Lambda([_x], smt.And(Int0(_x), _x.int >= 0))
Bool0 = smt.Lambda([_x], _x.is_Bool)
Real0 = smt.Lambda([_x], _x.is_Real)
Unit0 = smt.Lambda([_x], smt.And(_x.is_Bool, _x.bool == smt.BoolVal(True)))

# Polymorphic definitions
neg = kd.notation.neg.define(
    [_x],
    kd.cond(
        (_x.is_Bool, Type0.Bool(_x.bool)),
        (_x.is_Int, Type0.Int(-_x.int)),
        (_x.is_Real, Type0.Real(-_x.real)),
    ),
)

"""

def from_dt(dt : smt.DatatypeSortRef) -> smt.ExprRef:
    # encode x to tagged sequences
    kd.cond(
      *[dt.recognizer(i), smt.Concat(smt.Unit(Type0.IntVal(i)), smt.Unit(dt.accessor(i,0)(x))) for i in range(dt.num_constructors())])
      )
def to_set(dt : smt.DatatypeSortRef) -> smt.ExprRef:
    # set corresponding to encoding
    # smt.Exists([z], from_dt(dt)(z) == x)
    # but there is a more computational version.
kd.prove(forall([x], to_set(dt)(from_dt(dt))) # encoding is in encoding.
def to_dt(dt : smt.DatatypeSortRef) -> smt.ExprRef:
    # decode tagged sequences to x

class OpenFuncDecl:
    name : str
    domains : tuple[smt.SortRef]
    range : smt.SortRef
    head : smt.FuncDeclRef
    last : smt.FuncDeclRef
    defns : list[smt.FuncDeclRef] = []
    undef : smt.FuncDeclRef
    def __init__(self, name : str, *sorts : smt.SortRef):
        self.name = name
        self.defns = []
        self.undef = kd.FuncDecl(name, sorts, sorts[-1])
    def define(self, vs, cond, body) -> smt.FuncDeclRef:
        assert [v.sort() ==  s for v,s in zip(vs, self.sorts]
        assert body.sort() == self.range
        newundef = smt.FreshFunction(*[v.sort() for v in vs], self.range)
        self.defns.append(kd.define(self.last.name(), vs, smt.If(cond, body, newundef(*vs)))
        self.undef = newundef
        

def Seq(T : smt.FuncRef) -> smt.QuantifierRef:
    x = smt.FreshConst("x", T.domain())
    return smt.Lambda([x], smt.And(x.is_Seq, smt.SeqFoldLeftsmt.True, T, (x.seq)
def Vec(n, T : smt.FuncRef) -> smt.QuantifierRef:
    x = smt.FreshConst("x", T.domain())
    return smt.Lambda([x], smt.And(Seq(T)(x), smt.Length(x.seq) == n))
def Id(T, x, y) -> smt.QuantifierRef:
    p = smt.FreshConst("p", T.domain())
    return smt.Lambda([p], smt.And(Unit(p) , x == y))



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

def Int(x : smt.ExprRef) -> smt.BoolRef:


def level(x : smt.ExprRef) -> smt.IntRef:
    x.sort().name()
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
