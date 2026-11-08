"""
Algebraic datatype of lists.

You may prefer using theories.seq which offers more builtin support for things like associativity.
"""

import kdrag as kd
from kdrag import define
import kdrag.smt as smt
from kdrag.smt import BoolSort, Consts, Function, If, Int, IntSort, IntVal, Or
import functools

ListSort = kd.ListSort


class List_:
    # https://ocaml.org/manual/5.3/api/List.html
    # https://www.why3.org/stdlib/list.html
    # https://rocq-prover.org/doc/V9.0.0/stdlib/Stdlib.Lists.List.html

    def __init__(self, Elt: smt.SortRef):
        """
        >>> _ = List(IntSort())
        """
        self.Elt = Elt
        T = ListSort(Elt)
        name = T.sexpr()
        self.T = T
        self.Cons = T.Cons
        self.Nil = T.Nil
        x, y, z = Consts("x y z", Elt)
        l, l1, l2 = Consts("l l1 l2", T)
        assert isinstance(l, smt.DatatypeRef) and isinstance(
            l1, smt.DatatypeRef
        )  # type checking
        length = Function(T.sexpr() + ".length", T, IntSort())
        self.length = define(name + ".length", [l], If(l.is_Nil, 0, 1 + length(l.tail)))

        n = Int("n")
        nth = Function(name + ".nth", self.T, IntSort(), self.Elt)
        self.nth = define(name + ".nth", [l, n], If(n <= 0, l.head, nth(l.tail, n - 1)))
        mem = Function(name + ".mem", self.Elt, self.T, BoolSort())
        self.mem = define(
            name + ".mem",
            [x, l],
            If(l.is_Nil, False, Or(l.head == x, mem(x, l.tail))),
        )
        append = Function(name + ".append", T, T, T)
        self.append = define(
            name + ".append",
            [l1, l2],
            If(l1.is_Nil, l2, self.Cons(l1.head, append(l1.tail, l2))),
        )
        kd.notation.add.register(T, self.append)
        rev = Function(name + ".rev", T, T)
        self.rev = define(
            name + ".rev",
            [l],
            If(l.is_Nil, self.Nil, rev(l.tail) + self.Cons(l.head, self.Nil)),
        )

    def of_list(self, xs: list[smt.ExprRef]) -> smt.DatatypeRef:
        """
        Helper to construct List values
        >>> IntList = List(IntSort())
        >>> IntList.of_list([1, 2, 3])
        Cons(1, Cons(2, Cons(3, Nil)))
        """
        if len(xs) == 0:
            return self.Nil
        acc = self.Nil
        for a in reversed(xs):
            acc = self.Cons(IntVal(a), acc)
        return acc


@functools.cache
def List(Elt: smt.SortRef) -> List_:
    """
    >>> IntList = List(IntSort())
    >>> IntList.Cons(1, IntList.Nil)
    Cons(1, Nil)
    """
    return List_(Elt)
