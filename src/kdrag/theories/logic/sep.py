from kdrag import QExists, QForAll, define, prove  # noqa: F401
import kdrag.theories.set as set_
import kdrag.smt as smt
from kdrag.smt import (  # noqa: F401
    ArraySort,
    BitVec,
    BitVecSort,
    BoolSort,
    BoolVal,
    Const,
    Consts,
    ForAll,
    FreshConst,
    Int,
    Lambda,
    Store,
)
import functools

type PropRef = smt.FuncRef


class Sep:
    """
    A model of seperation logic using sets as a partial monoid.

    >>> Sep8 = make_sep(BitVecSort(8))
    >>> p, q = Sep8.Props("p q")
    >>> h = Const("h", Sep8.AllocSort)
    >>> _ = prove(ForAll([h], Sep8.Sep(p, q)[h] == Sep8.Sep(q, p)[h]))
    >>> _ = prove(ForAll([h], Sep8.Sep(p, Sep8.Emp)[h] == p[h]))
    """

    def __init__(self, KeySort: smt.SortRef):
        self.KeySort = KeySort
        self.AllocSort = set_.Set(KeySort)
        self.PropSort = ArraySort(self.AllocSort, BoolSort())

        key = Const("key", KeySort)
        h = Const("h", self.AllocSort)
        p, q, r = Consts("p q r", self.PropSort)
        self.Emp = Lambda([h], h == self.AllocSort.empty)
        self.emp = define("emp", [], self.Emp)
        self.sep = define("sep", [p, q], self.Sep(p, q))
        self.alloc = define("alloc", [key], self.Alloc(key))
        self.true = Lambda([h], BoolVal(True))
        self.false = Lambda([h], BoolVal(False))
        self.wand = define("wand", [p, q], self.Wand(p, q))

    def Lift(self, expr: smt.ExprRef):
        """
        Lift an expression into constant function on heap.

        >>> Sep8 = make_sep(BitVecSort(8))
        >>> p = Int("p")
        >>> Sep8.Lift(p)
        Lambda(h!..., p)
        """
        h = FreshConst(self.AllocSort, prefix="h")
        return Lambda([h], expr)

    def Alloc(self, key):
        """
        Alloc(key) is a predicate that exactly key is allocated in current heap

        >>> Sep8 = make_sep(BitVecSort(8))
        >>> key = BitVec("key", 8)
        >>> Sep8.Alloc(key)
        Lambda(h!..., h!... == Store(K(BitVec(8), False), key, True))
        """
        h = FreshConst(self.AllocSort, prefix="h")
        return Lambda([h], h == Store(self.AllocSort.empty, key, True))

    def Pto(self, key, v):
        """
        Pto(key, v) says that key is allocated but separately a special variable call heap has value v at location key.

        >>> Sep8 = make_sep(BitVecSort(8))
        >>> key = BitVec("key", 8)
        >>> v = BitVec("v", 8)
        >>> Sep8.Pto(key, v)
        Lambda(h!...,
           And(Lambda(h!...,
                      h!... ==
                      Store(K(BitVec(8), False), key, True))[h!...],
               Lambda(h!..., heap[key] == v)[h!...]))
        """
        # TODO: expand out to make cleaner
        # Is this even a good idea?
        heap = Const("heap", ArraySort(self.KeySort, v.sort()))
        return self.And(self.Alloc(key), self.Lift(heap[key] == v))

    def Sep(self, a, b):  # multistar *args?
        """
        Separating conjunction

        """
        h = FreshConst(self.AllocSort, prefix="h")
        k = FreshConst(self.AllocSort, prefix="k")
        return Lambda([h], QExists([k], k <= h, a[h - k] & b[k]))

    def Wand(self, a, b):
        h = FreshConst(self.AllocSort, prefix="h")
        k = FreshConst(self.AllocSort, prefix="k")
        return Lambda([h], QForAll([k], k & h == self.AllocSort.empty, a[k], b[k | h]))

    def And(self, *args):
        """
        Lifted And

        >>> Sep8 = make_sep(BitVecSort(8))
        >>> p, q = Sep8.Props("p q")
        >>> Sep8.And(p, q)
        Lambda(h!..., And(p[h!...], q[h!...]))
        """
        h = FreshConst(self.AllocSort, prefix="h")
        return Lambda([h], smt.And([a[h] for a in args]))

    def Or(self, *args):
        h = FreshConst(self.AllocSort, prefix="h")
        return Lambda([h], smt.Or([a[h] for a in args]))

    def Implies(self, a: PropRef, b: PropRef) -> PropRef:
        h = FreshConst(self.AllocSort, prefix="h")
        assert isinstance(a, smt.ArrayRef) or isinstance(a, smt.QuantifierRef)
        assert isinstance(b, smt.ArrayRef) or isinstance(b, smt.QuantifierRef)
        return Lambda([h], smt.Implies(a[h], b[h]))

    def Prop(self, name: str):
        """
        A named separation logic proposition
        """
        return Const(name, self.PropSort)

    def Props(self, names: str):
        return Consts(names, self.PropSort)

    def Valid(self, prop: PropRef) -> smt.BoolRef:
        """
        Valid converts a predicate on heaps into the boolean expression stating it is true for
        all heaps (semantically valid).
        """
        h = FreshConst(self.AllocSort, prefix="h")
        assert isinstance(h, smt.ArrayRef)
        assert isinstance(prop, smt.ArrayRef) or isinstance(prop, smt.QuantifierRef)
        return ForAll([h], prop[h])


@functools.cache
def make_sep(KeySort: smt.SortRef) -> Sep:
    return Sep(KeySort)
