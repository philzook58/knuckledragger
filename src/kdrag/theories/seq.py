"""
Built in smtlib theory of finite sequences.
"""

import kdrag as kd
from kdrag import QForAll, axiom, prove
import kdrag.smt as smt
from kdrag.smt import (  # noqa: F401
    And,
    BoolSort,
    Concat,
    Const,
    Consts,
    Contains,
    Empty,
    ForAll,
    FreshConst,
    Function,
    Implies,
    IntSort,
    IntVal,
    Ints,
    Length,
    SeqSort,
    SubSeq,
    simplify,
)


# induct_list List style induction
# induct_snoc
# concat induction
# Strong induction


def induct_list(x: smt.SeqRef, P):
    """

    >>> x = Const("x", Seq(IntSort()))
    >>> P = Function("P", Seq(IntSort()), BoolSort())
    >>> induct_list(x, P)
    |= Implies(And(P(Empty(Seq(Int))),
                ForAll([hd!..., tl!...],
                      Implies(P(tl!...),
                              P(Concat(Unit(hd!...), tl!...))))),
            P(x))
    """
    assert isinstance(x, smt.SeqRef)
    hd = FreshConst(x.sort().basis(), prefix="hd")
    tl = FreshConst(x.sort(), prefix="tl")
    return axiom(
        Implies(
            And(
                P(Empty(x.sort())),
                QForAll([hd, tl], P(tl), P(smt.Unit(hd) + tl)),
            ),
            P(x),
        )
    )


"""
def induct(T: smt.SortRef, P) -> kd.kernel.Proof:
    z = smt.FreshConst(T, prefix="z")
    sort = smt.SeqSort(T)
    x, y = smt.FreshConst(sort), smt.FreshConst(sort)
    return kd.axiom(
        smt.And(
            P(smt.Empty(sort)),
            kd.QForAll([z], P(smt.Unit(z))),
            kd.QForAll([x, y], P(x), P(y), P(smt.Concat(x, y))),
        )  # -------------------------------------------------
        == kd.QForAll([x], P(x))
    )
"""

induct = kd.notation.induct_seq

seq = kd.seq


def Cons(x: smt.ExprRef, tl: smt.SeqSortRef):
    """
    >>> simplify(Cons(IntVal(3), Nil(IntSort())))
    Unit(3)
    """
    return Concat([smt.Unit(x), tl])


def Nil(s: smt.SortRef):
    return Empty(SeqSort(s))


def Seq(T: smt.SortRef) -> smt.SeqSortRef:
    """
    Make sort of Sequences and prove useful lemmas.

    >>> BoolSeq = Seq(BoolSort())
    >>> x,y,z = Consts("x y z", BoolSeq)
    >>> x + y
    Concat(x, y)
    """
    S = SeqSort(T)
    smt.sort_registry[S.get_id()] = S
    x, y, z = Consts("x y z", S)
    empty = Empty(S)
    S.empty = empty

    S.concat_empty = prove(QForAll([x], empty + x == x))
    S.empty_concat = prove(QForAll([x], x + empty == x))
    S.concat_assoc = prove(
        QForAll(
            [x, y, z],
            (x + y) + z == x + (y + z),
        )
    )

    S.length_empty = prove(QForAll([x], Length(empty) == 0))
    S.length_unit = prove(QForAll([x], Length(smt.Unit(x)) == 1))
    S.concat_length = prove(QForAll([x, y], Length(x + y) == Length(x) + Length(y)))
    S.length_zero_unique = prove(QForAll([x], (Length(x) == 0) == (x == empty)))
    S.concat_head = prove(
        QForAll(
            [x],
            Length(x) > 0,
            smt.Unit(x[0]) + SubSeq(x, 1, Length(x) - 1) == x,
        )
    )

    n, m = Ints("n m")

    S.subseq_zero = prove(QForAll([x, n], SubSeq(x, n, 0) == empty))
    S.subseq_length = prove(
        QForAll(
            [x, n, m],
            m >= 0,
            n >= 0,
            n + m <= Length(x),
            Length(SubSeq(x, n, m)) == m,
        )
    )
    S.subseq_all = prove(QForAll([x], SubSeq(x, 0, Length(x)) == x))
    S.subseq_concat = prove(
        QForAll(
            [x, n],
            n >= 0,
            n <= Length(x),
            SubSeq(x, 0, n) + SubSeq(x, n, Length(x) - n) == x,
        )
    )

    # S.head_length = kd.prove(
    #    kd.QForAll(
    #        [x], smt.Length(x) != 0, x[0] + smt.SubSeq(x, 1, smt.Length(x) - 1) == x
    #    )
    # )
    S.contains_empty = prove(ForAll([x], Contains(x, empty)))
    S.contains_self = prove(ForAll([x], Contains(x, x)))
    S.contains_concat_left = prove(
        QForAll([x, y, z], Contains(x, z), Contains(x + y, z))
    )
    S.contains_concat_right = prove(
        QForAll([x, y, z], Contains(y, z), Contains(x + y, z))
    )
    S.contains_subseq = prove(ForAll([x], Contains(x, SubSeq(x, n, m))))
    # self.contains_unit = kd.kernel.prove(
    #    kd.QForAll([x, y], smt.Contains(smt.Unit(x), y) == (smt.Unit(x) == y))
    # )
    S.empty_contains = kd.kernel.prove(QForAll([x], Contains(empty, x), (x == empty)))

    # InRe, Extract, IndexOf, LastIndexOf, prefixof, replace, suffixof
    # SeqMap, SeqMapI, SeqFoldLeft, SeqFoldLeftI
    # Contains
    return S


def Unit(x: smt.ExprRef) -> smt.SeqRef:
    """
    Construct a sequence of length 1.
    """
    return smt.Unit(x)
