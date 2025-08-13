import kdrag as kd
import kdrag.theories.set as set_
import kdrag.smt as smt
import functools

type PropRef = smt.ArrayRef | smt.QuantifierRef


class Sep:
    """
    A model of seperation logic using sets as a partial monoid.

    >>> Sep8 = make_sep(smt.BitVecSort(8))
    >>> p, q = Sep8.Props("p q")
    >>> h = smt.Const("h", Sep8.AllocSort)
    >>> _ = kd.prove(smt.ForAll([h], Sep8.Sep(p, q)[h] == Sep8.Sep(q, p)[h]))
    >>> _ = kd.prove(smt.ForAll([h], Sep8.Sep(p, Sep8.Emp)[h] == p[h]))
    """

    def __init__(self, KeySort: smt.SortRef):
        self.KeySort = KeySort
        self.AllocSort = set_.Set(KeySort)
        self.PropSort = smt.ArraySort(self.AllocSort, smt.BoolSort())

        key = smt.Const("key", KeySort)
        h = smt.Const("h", self.AllocSort)
        p, q, r = smt.Consts("p q r", self.PropSort)
        self.Emp = smt.Lambda([h], h == self.AllocSort.empty)
        self.emp = kd.define("emp", [], self.Emp)
        self.sep = kd.define("sep", [p, q], self.Sep(p, q))
        self.alloc = kd.define("alloc", [key], self.Alloc(key))
        self.true = smt.Lambda([h], smt.BoolVal(True))
        self.false = smt.Lambda([h], smt.BoolVal(False))
        self.wand = kd.define("wand", [p, q], self.Wand(p, q))

    def Lift(self, expr: smt.ExprRef):
        """
        Lift an expression into constant function on heap.

        >>> Sep8 = make_sep(smt.BitVecSort(8))
        >>> p = smt.Int("p")
        >>> Sep8.Lift(p)
        Lambda(h!..., p)
        """
        h = smt.FreshConst(self.AllocSort, prefix="h")
        return smt.Lambda([h], expr)

    def Alloc(self, key):
        """
        Alloc(key) is a predicate that exactly key is allocated in current heap

        >>> Sep8 = make_sep(smt.BitVecSort(8))
        >>> key = smt.BitVec("key", 8)
        >>> Sep8.Alloc(key)
        Lambda(h!..., h!... == Store(K(BitVec(8), False), key, True))
        """
        h = smt.FreshConst(self.AllocSort, prefix="h")
        return smt.Lambda([h], h == smt.Store(self.AllocSort.empty, key, True))

    def Pto(self, key, v):
        """
        Pto(key, v) says that key is allocated but separately a special variable call heap has value v at location key.

        >>> Sep8 = make_sep(smt.BitVecSort(8))
        >>> key = smt.BitVec("key", 8)
        >>> v = smt.BitVec("v", 8)
        >>> Sep8.Pto(key, v)
        Lambda(h!...,
           And(Lambda(h!...,
                      h!... ==
                      Store(K(BitVec(8), False), key, True))[h!...],
               Lambda(h!..., heap[key] == v)[h!...]))
        """
        # TODO: expand out to make cleaner
        # Is this even a good idea?
        heap = smt.Const("heap", smt.ArraySort(self.KeySort, v.sort()))
        return self.And(self.Alloc(key), self.Lift(heap[key] == v))

    def Sep(self, a, b):  # multistar *args?
        """
        Separating conjunction

        """
        h = smt.FreshConst(self.AllocSort, prefix="h")
        k = smt.FreshConst(self.AllocSort, prefix="k")
        return smt.Lambda([h], kd.QExists([k], k <= h, a[h - k] & b[k]))

    def Wand(self, a, b):
        h = smt.FreshConst(self.AllocSort, prefix="h")
        k = smt.FreshConst(self.AllocSort, prefix="k")
        return smt.Lambda(
            [h], kd.QForAll([k], k & h == self.AllocSort.empty, a[k], b[k | h])
        )

    def And(self, *args):
        """
        Lifted And

        >>> Sep8 = make_sep(smt.BitVecSort(8))
        >>> p, q = Sep8.Props("p q")
        >>> Sep8.And(p, q)
        Lambda(h!..., And(p[h!...], q[h!...]))
        """
        h = smt.FreshConst(self.AllocSort, prefix="h")
        return smt.Lambda([h], smt.And([a[h] for a in args]))

    def Or(self, *args):
        h = smt.FreshConst(self.AllocSort, prefix="h")
        return smt.Lambda([h], smt.Or([a[h] for a in args]))

    def Implies(self, a: PropRef, b: PropRef) -> PropRef:
        h = smt.FreshConst(self.AllocSort, prefix="h")
        return smt.Lambda([h], smt.Implies(a[h], b[h]))

    def Prop(self, name: str):
        """
        A named separation logic proposition
        """
        return smt.Const(name, self.PropSort)

    def Props(self, names: str):
        return smt.Consts(names, self.PropSort)

    def Valid(self, prop: PropRef) -> smt.BoolRef:
        """
        Valid converts a predicate on heaps into the boolean expression stating it is true for
        all heaps (semantically valid).
        """
        h = smt.FreshConst(self.Alloc, prefix="h")
        return smt.ForAll([h], prop[h])


@functools.cache
def make_sep(KeySort: smt.SortRef) -> Sep:
    return Sep(KeySort)
