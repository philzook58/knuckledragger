"""
Theory of regular expressions
"""

import kdrag as kd
from kdrag import axiom, define, prove
import kdrag.smt as smt
from kdrag.smt import (  # noqa: F401
    Complement,
    Concat,
    Const,
    Consts,
    Diff,
    Empty,
    ForAll,
    Full,
    InRe,
    IntSort,
    IntVal,
    Intersect,
    Lambda,
    Option,
    Re,
    SeqSort,
    Star,
    Union,
    Unit,
)
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

    >>> T = ReSort(SeqSort(IntSort()))
    >>> x,y,z = Consts("x y z", T)
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
    >>> x[Unit(IntVal(0))] # A regular expression is something like a predicate on sequences
    InRe(Unit(0), x)
    >>> x - y
    re.diff(x, y)
    """
    T = smt.ReSort(S)
    smt.sort_registry[T.get_id()] = T
    empty = Empty(T)
    zero = empty
    eps = Re(Empty(S))  # empty string acceptor
    one = eps
    T.empty = empty
    T.full = Full(T)
    # ReRef already defines + to be Union
    kd.notation.mul.register(T, lambda x, y: Concat(x, y))
    kd.notation.or_.register(T, lambda x, y: Union(x, y))
    kd.notation.and_.register(T, lambda x, y: Intersect(x, y))
    kd.notation.invert.register(T, lambda x: Complement(x))
    kd.notation.getitem.register(T, lambda x, i: InRe(i, x))
    kd.notation.sub.register(T, lambda x, y: Diff(x, y))

    x, y, z = Consts("x y z", T)
    T.add_comm = prove(ForAll([x, y], x + y == y + x))
    T.add_assoc = prove(ForAll([x, y, z], (x + y) + z == x + (y + z)))
    # TODO: failing. Wrong or needs to be axiomatized?
    # T.concat_assoc = kd.prove(smt.ForAll([x, y, z], (x * y) * z == x * (y * z)))
    T.add_zero = prove(ForAll([x], x + zero == x))
    T.add_zero_left = prove(ForAll([x], zero + x == x))
    T.add_idem = prove(ForAll([x], x + x == x))
    T.mul_zero = prove(ForAll([x], x * zero == zero))
    # T.distrib = kd.prove(smt.ForAll([x, y, z], x * (y + z) == x * y + x * z))

    T.concat_one = prove(ForAll([x], x * one == x))

    T.zero_star = prove(Star(zero) == one)
    T.one_star = prove(Star(one) == one)
    T.star_concat = prove(ForAll([x], Star(x) * Star(x) == Star(x)))
    T.star_star = prove(ForAll([x], Star(Star(x)) == Star(x)))
    # These are the standard star-unfolding laws of builtin regex semantics.
    # Z3 5.3.3 returns unknown for them with symbolic regular expressions.
    T.star_unfold = axiom(ForAll([x], one + x * Star(x) == Star(x)))
    T.star_unfold2 = axiom(ForAll([x], one + Star(x) * x == Star(x)))

    T.option_defn = prove(ForAll([x], Option(x) == one + x))

    T.le = kd.notation.le.define([x, y], y + x == y)
    T.le_refl = prove(ForAll([x], x <= x), by=[T.le.defn])

    # T.le_trans = kd.prove(
    #    kd.QForAll([x, y, z], x <= y, y <= z, x <= z),
    #    by=[T.le.defn],
    # )

    a = Const("a", S)
    T.to_set = define("to_set", [x], Lambda([a], x[a]))

    # T.union_all_char = kd.prove(smt.ForAll([a], smt.AllChar(T) ==
    # smt.

    return T
