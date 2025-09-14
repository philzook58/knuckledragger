"""
Theory of regular expressions
"""

import kdrag as kd
import kdrag.smt as smt
import functools

"""
Some of the z3 builtins on Regular Expressions:

ReStr = smt.ReSort(smt.SeqSort(smt.IntSort()))
r1 = smt.Full(ReStr)
smt.AllChar(ReStr)
smt.Complement(r1)
smt.Concat(r1, r1)
smt.Diff(r1, r1)
smt.Empty(ReStr)
re = smt.Union(smt.Re("a"),smt.Re("b"))
smt.simplify(smt.InRe("a", re))
smt.Intersect(re, re)
smt.Loop(re, 0, 10)
smt.Option(re)
smt.Plus(re)
smt.Range("a", "z")
smt.Re("abc") # literal match
smt.Re(smt.Unit(smt.BoolVal(True)))
smt.Star(re)
"""


@functools.cache
def ReSort(S: smt.SortRef) -> smt.ReSortRef:
    """
    Regular expression sort. Sort parameter needs to be a sequence sort.
    https://en.wikipedia.org/wiki/Kleene_algebra

    >>> T = ReSort(smt.SeqSort(smt.IntSort()))
    >>> x,y,z = smt.Consts("x y z", T)
    >>> x + y
    Union(x, y)
    >>> x | y
    Union(x, y)
    >>> x * y
    re.++(x, y)
    >>> x & y
    Intersect(x, y)
    >>> ~x
    Complement(x)
    >>> x[smt.Unit(smt.IntVal(0))] # A regular expression is something like a predicate on sequences
    InRe(Unit(0), x)
    >>> x - y
    re.diff(x, y)
    """
    T = smt.ReSort(S)
    smt.sort_registry[T.get_id()] = T
    empty = smt.Empty(T)
    zero = empty
    eps = smt.Re(smt.Empty(S))  # empty string acceptor
    one = eps
    T.empty = empty
    T.full = smt.Full(T)
    # ReRef already defines + to be Union
    kd.notation.mul.register(T, lambda x, y: smt.Concat(x, y))
    kd.notation.or_.register(T, lambda x, y: smt.Union(x, y))
    kd.notation.and_.register(T, lambda x, y: smt.Intersect(x, y))
    kd.notation.invert.register(T, lambda x: smt.Complement(x))
    kd.notation.getitem.register(T, lambda x, i: smt.InRe(i, x))
    kd.notation.sub.register(T, lambda x, y: smt.Diff(x, y))

    x, y, z = smt.Consts("x y z", T)
    T.add_comm = kd.prove(smt.ForAll([x, y], x + y == y + x))
    T.add_assoc = kd.prove(smt.ForAll([x, y, z], (x + y) + z == x + (y + z)))
    # TODO: failing. Wrong or needs to be axiomatized?
    # T.concat_assoc = kd.prove(smt.ForAll([x, y, z], (x * y) * z == x * (y * z)))
    T.add_zero = kd.prove(smt.ForAll([x], x + zero == x))
    T.add_zero_left = kd.prove(smt.ForAll([x], zero + x == x))
    T.add_idem = kd.prove(smt.ForAll([x], x + x == x))
    T.mul_zero = kd.prove(smt.ForAll([x], x * zero == zero))
    # T.distrib = kd.prove(smt.ForAll([x, y, z], x * (y + z) == x * y + x * z))

    T.concat_one = kd.prove(smt.ForAll([x], x * one == x))

    T.zero_star = kd.prove(smt.Star(zero) == one)
    T.one_star = kd.prove(smt.Star(one) == one)
    T.star_concat = kd.prove(smt.ForAll([x], smt.Star(x) * smt.Star(x) == smt.Star(x)))
    T.star_star = kd.prove(smt.ForAll([x], smt.Star(smt.Star(x)) == smt.Star(x)))
    T.star_unfold = kd.prove(smt.ForAll([x], one + x * smt.Star(x) == smt.Star(x)))
    T.star_unfold2 = kd.prove(smt.ForAll([x], one + smt.Star(x) * x == smt.Star(x)))

    T.option_defn = kd.prove(smt.ForAll([x], smt.Option(x) == one + x))

    T.le = kd.notation.le.define([x, y], y + x == y)
    T.le_refl = kd.prove(smt.ForAll([x], x <= x), by=[T.le.defn])

    # T.le_trans = kd.prove(
    #    kd.QForAll([x, y, z], x <= y, y <= z, x <= z),
    #    by=[T.le.defn],
    # )

    a = smt.Const("a", S)
    T.to_set = kd.define("to_set", [x], smt.Lambda([a], x[a]))

    # T.union_all_char = kd.prove(smt.ForAll([a], smt.AllChar(T) ==
    # smt.

    return T
