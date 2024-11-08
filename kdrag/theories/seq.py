import kdrag as kd
import kdrag.smt as smt

"""
Built in smtlib theory of finite sequences.
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


class Seq:
    def __init__(self, T):
        self.T = T
        sort = smt.SeqSort(T)
        empty = smt.Empty(sort)
        self.empty = empty
        x, y, z = smt.Consts("x y z", sort)
        # TODO: seq needs well formedness condition inherited from elements

        self.concat_empty = kd.kernel.lemma(
            kd.QForAll([x], smt.Concat(smt.Empty(sort), x) == x)
        )
        self.empty_concat = kd.kernel.lemma(
            kd.QForAll([x], smt.Concat(x, smt.Empty(sort)) == x)
        )
        self.concat_assoc = kd.kernel.lemma(
            kd.QForAll(
                [x, y, z],
                smt.Concat(x, smt.Concat(y, z)) == smt.Concat(smt.Concat(x, y), z),
            )
        )
        self.concat_length = kd.kernel.lemma(
            kd.QForAll(
                [x, y], smt.Length(smt.Concat(x, y)) == smt.Length(x) + smt.Length(y)
            )
        )
        self.length_empty = kd.kernel.lemma(
            kd.QForAll([x], (smt.Length(x) == 0) == (x == empty))
        )
        """
        self.contains_concat_left = kd.kernel.lemma(
            kd.QForAll(
                [x, y, z], smt.Contains(x, z) == smt.Contains(smt.Concat(x, y), z)
            )
        )
        self.contains_concat_right = kd.kernel.lemma(
            kd.QForAll(
                [x, y, z], smt.Contains(y, z) == smt.Contains(smt.Concat(x, y), z)
            )
        )"""
        # self.contains_unit = kd.kernel.lemma(
        #    kd.QForAll([x, y], smt.Contains(smt.Unit(x), y) == (x == y))
        # )
        """
        self.contains_empty = kd.kernel.lemma(
            kd.QForAll([x], smt.Contains(smt.Empty(T), x) == (x == smt.Empty(T)))
        )"""
        # InRe, Extract, IndexOf, LastIndexOf, prefixof, replace, suffixof
        # SeqMap, SeqMapI, SeqFoldLeft, SeqFoldLeftI
