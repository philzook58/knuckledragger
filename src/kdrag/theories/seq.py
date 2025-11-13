"""
Built in smtlib theory of finite sequences.
"""

import kdrag as kd
import kdrag.smt as smt


# induct_list List style induction
# induct_snoc
# concat induction
# Strong induction


def induct_list(x: smt.SeqRef, P):
    """

    >>> x = smt.Const("x", Seq(smt.IntSort()))
    >>> P = smt.Function("P", Seq(smt.IntSort()), smt.BoolSort())
    >>> induct_list(x, P)
    |= Implies(And(P(Empty(Seq(Int))),
                ForAll([hd!..., tl!...],
                      Implies(P(tl!...),
                              P(Concat(Unit(hd!...), tl!...))))),
            P(x))
    """
    assert isinstance(x, smt.SeqRef)
    hd = smt.FreshConst(x.sort().basis(), prefix="hd")
    tl = smt.FreshConst(x.sort(), prefix="tl")
    return kd.axiom(
        smt.Implies(
            smt.And(
                P(smt.Empty(x.sort())),
                kd.QForAll([hd, tl], P(tl), P(smt.Unit(hd) + tl)),
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
    >>> smt.simplify(Cons(smt.IntVal(3), Nil(smt.IntSort())))
    Unit(3)
    """
    return smt.Concat([smt.Unit(x), tl])


def Tail(s: smt.SeqSortRef):
    """
    >>> x = smt.Const("x", Seq(smt.BoolSort()))
    >>> Tail(x)
    seq.extract(x, 1, Length(x) - 1)
    """
    return smt.SubSeq(s, 1, smt.Length(s) - 1)


def Nil(s: smt.SortRef):
    return smt.Empty(smt.SeqSort(s))


def Head(s: smt.SeqRef):
    """
    >>> x = smt.Const("x", Seq(smt.BoolSort()))
    >>> Head(x)
    Nth(x, 0)
    >>> kd.prove(smt.Implies(smt.Length(x) > 0, smt.Concat([smt.Unit(Head(x)), Tail(x)]) == x))
    |= Implies(Length(x) > 0,
        Concat(Unit(Nth(x, 0)),
                seq.extract(x, 1, Length(x) - 1)) ==
        x)
    """
    return s[0]


def Seq(T: smt.SortRef) -> smt.SeqSortRef:
    """
    Make sort of Sequences and prove useful lemmas.

    >>> BoolSeq = Seq(smt.BoolSort())
    >>> x,y,z = smt.Consts("x y z", BoolSeq)
    >>> x + y
    Concat(x, y)
    """
    S = smt.SeqSort(T)
    smt.sort_registry[S.get_id()] = S
    x, y, z = smt.Consts("x y z", S)
    empty = smt.Empty(S)
    S.empty = empty

    S.concat_empty = kd.prove(kd.QForAll([x], empty + x == x))
    S.empty_concat = kd.prove(kd.QForAll([x], x + empty == x))
    S.concat_assoc = kd.prove(
        kd.QForAll(
            [x, y, z],
            (x + y) + z == x + (y + z),
        )
    )

    S.length_empty = kd.prove(kd.QForAll([x], smt.Length(empty) == 0))
    S.length_unit = kd.prove(kd.QForAll([x], smt.Length(smt.Unit(x)) == 1))
    S.concat_length = kd.prove(
        kd.QForAll([x, y], smt.Length(x + y) == smt.Length(x) + smt.Length(y))
    )
    S.length_zero_unique = kd.prove(
        kd.QForAll([x], (smt.Length(x) == 0) == (x == empty))
    )
    S.concat_head = kd.prove(
        kd.QForAll(
            [x],
            smt.Length(x) > 0,
            smt.Unit(x[0]) + smt.SubSeq(x, 1, smt.Length(x) - 1) == x,
        )
    )

    n, m = smt.Ints("n m")

    S.subseq_zero = kd.prove(kd.QForAll([x, n], smt.SubSeq(x, n, 0) == empty))
    S.subseq_length = kd.prove(
        kd.QForAll(
            [x, n, m],
            m >= 0,
            n >= 0,
            n + m <= smt.Length(x),
            smt.Length(smt.SubSeq(x, n, m)) == m,
        )
    )
    S.subseq_all = kd.prove(kd.QForAll([x], smt.SubSeq(x, 0, smt.Length(x)) == x))
    S.subseq_concat = kd.prove(
        kd.QForAll(
            [x, n],
            n >= 0,
            n <= smt.Length(x),
            smt.SubSeq(x, 0, n) + smt.SubSeq(x, n, smt.Length(x) - n) == x,
        )
    )

    # S.head_length = kd.prove(
    #    kd.QForAll(
    #        [x], smt.Length(x) != 0, x[0] + smt.SubSeq(x, 1, smt.Length(x) - 1) == x
    #    )
    # )
    S.contains_empty = kd.prove(smt.ForAll([x], smt.Contains(x, empty)))
    S.contains_self = kd.prove(smt.ForAll([x], smt.Contains(x, x)))
    S.contains_concat_left = kd.prove(
        kd.QForAll([x, y, z], smt.Contains(x, z), smt.Contains(x + y, z))
    )
    S.contains_concat_right = kd.prove(
        kd.QForAll([x, y, z], smt.Contains(y, z), smt.Contains(x + y, z))
    )
    S.contains_subseq = kd.prove(smt.ForAll([x], smt.Contains(x, smt.SubSeq(x, n, m))))
    # self.contains_unit = kd.kernel.prove(
    #    kd.QForAll([x, y], smt.Contains(smt.Unit(x), y) == (smt.Unit(x) == y))
    # )
    S.empty_contains = kd.kernel.prove(
        kd.QForAll([x], smt.Contains(empty, x), (x == empty))
    )

    # InRe, Extract, IndexOf, LastIndexOf, prefixof, replace, suffixof
    # SeqMap, SeqMapI, SeqFoldLeft, SeqFoldLeftI
    # Contains
    return S


def Unit(x: smt.ExprRef) -> smt.SeqRef:
    """
    Construct a sequence of length 1.
    """
    return smt.Unit(x)
