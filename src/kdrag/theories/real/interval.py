import kdrag as kd
from kdrag import QForAll, Struct, define, prove
import kdrag.theories.real as R
from kdrag.smt import (
    And,
    Consts,
    ForAll,
    If,
    Implies,
    Ints,
    IsSubset,
    Lambda,
    RealVal,
    Reals,
    SetIntersect,
    SetUnion,
)

"""
Interval arithmetic. Intervals are a record of hi and lo bounds.
"""
Interval = Struct("Interval", ("lo", kd.R), ("hi", kd.R))
x, y, z = Reals("x y z")
i, j, k, I, J, K = Consts("i j k I J K", Interval)

setof = define("Interval.setof", [i], Lambda([x], And(i.lo <= x, x <= i.hi)))

kd.notation.getitem.register(Interval, lambda a, idx: setof(a)[idx])

meet = define("meet", [i, j], Interval.mk(R.max(i.lo, j.lo), R.min(i.hi, j.hi)))
meet_intersect = prove(
    ForAll([i, j], SetIntersect(setof(i), setof(j)) == setof(meet(i, j))),
    by=[setof.defn, meet.defn, R.min.defn, R.max.defn],
)
kd.notation.and_.register(Interval, meet)

join = define("join", [i, j], Interval.mk(R.min(i.lo, j.lo), R.max(i.hi, j.hi)))
join_union = prove(
    ForAll([i, j], IsSubset(SetUnion(setof(i), setof(j)), setof(join(i, j)))),
    by=[setof.defn, join.defn, R.min.defn, R.max.defn],
)
kd.notation.or_.register(Interval, join)

is_empty = define("is_empty", [I], i.hi > i.lo)
empty = define("empty", [], Interval.mk(RealVal(1), RealVal(0)))

width = define("width", [i], i.hi - i.lo)
mid = define("mid", [i], (i.lo + i.hi) / 2)

add = kd.notation.add.define([i, j], Interval.mk(i.lo + j.lo, i.hi + j.hi))
add_set = prove(
    ForAll([x, y, i, j], Implies(setof(i)[x] & setof(j)[y], setof(i + j)[x + y])),
    by=[add.defn, setof.defn],
)

sub = kd.notation.sub.define([i, j], Interval.mk(i.lo - j.hi, i.hi - j.lo))


sub_set = prove(
    QForAll([x, y, i, j], i[x], j[y], (i - j)[x - y]),
    by=[sub.defn, setof.defn],
)


def Min(xs):
    assert len(xs) > 0
    if len(xs) == 1:
        return xs[0]
    else:
        rest = xs[1:]
        return If(And([xs[0] <= x for x in rest]), xs[0], Min(rest))


def Max(xs):
    assert len(xs) > 0
    if len(xs) == 1:
        return xs[0]
    else:
        rest = xs[1:]
        return If(And([xs[0] >= x for x in rest]), xs[0], Min(rest))


x, y, z = Ints("x y z")

mul = define(
    "Interval.mul",
    [I, J],
    Interval.mk(
        Min([I.hi * J.hi, I.lo * J.lo, I.hi * J.lo, I.lo * J.hi]),
        Max([I.hi * J.hi, I.lo * J.lo, I.hi * J.lo, I.lo * J.hi]),
    ),
)


def test():
    """
    >>> True
    True
    """
