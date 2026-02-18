"""
Algebraic datatype of lists.

You may prefer using theories.seq which offers more builtin support for things like associativity.
"""

import kdrag as kd
import kdrag.smt as smt
import functools

ListSort = kd.ListSort


class List_:
    # https://ocaml.org/manual/5.3/api/List.html
    # https://www.why3.org/stdlib/list.html
    # https://rocq-prover.org/doc/V9.0.0/stdlib/Stdlib.Lists.List.html

    def __init__(self, Elt: smt.SortRef):
        """
        >>> _ = List(smt.IntSort())
        """
        self.Elt = Elt
        T = ListSort(Elt)
        name = T.sexpr()
        self.T = T
        self.Cons = T.Cons
        self.Nil = T.Nil
        x, y, z = smt.Consts("x y z", Elt)
        l, l1, l2 = smt.Consts("l l1 l2", T)
        assert isinstance(l, smt.DatatypeRef) and isinstance(
            l1, smt.DatatypeRef
        )  # type checking
        length = smt.Function(T.sexpr() + ".length", T, smt.IntSort())
        self.length = kd.define(
            name + ".length", [l], smt.If(l.is_Nil, 0, 1 + length(l.tail))
        )

        n = smt.Int("n")
        nth = smt.Function(name + ".nth", self.T, smt.IntSort(), self.Elt)
        self.nth = kd.define(
            name + ".nth", [l, n], smt.If(n <= 0, l.head, nth(l.tail, n - 1))
        )
        mem = smt.Function(name + ".mem", self.Elt, self.T, smt.BoolSort())
        self.mem = kd.define(
            name + ".mem",
            [x, l],
            smt.If(l.is_Nil, False, smt.Or(l.head == x, mem(x, l.tail))),
        )
        append = smt.Function(name + ".append", T, T, T)
        self.append = kd.define(
            name + ".append",
            [l1, l2],
            smt.If(l1.is_Nil, l2, self.Cons(l1.head, append(l1.tail, l2))),
        )
        kd.notation.add.register(T, self.append)
        rev = smt.Function(name + ".rev", T, T)
        self.rev = kd.define(
            name + ".rev",
            [l],
            smt.If(l.is_Nil, self.Nil, rev(l.tail) + self.Cons(l.head, self.Nil)),
        )

    def of_list(self, xs: list[smt.ExprRef]) -> smt.DatatypeRef:
        """
        Helper to construct List values
        >>> IntList = List(smt.IntSort())
        >>> IntList.of_list([1, 2, 3])
        Cons(1, Cons(2, Cons(3, Nil)))
        """
        if len(xs) == 0:
            return self.Nil
        acc = self.Nil
        for a in reversed(xs):
            acc = self.Cons(smt.IntVal(a), acc)
        return acc


@functools.cache
def List(Elt: smt.SortRef) -> List_:
    """
    >>> IntList = List(smt.IntSort())
    >>> IntList.Cons(1, IntList.Nil)
    Cons(1, Nil)
    """
    return List_(Elt)
