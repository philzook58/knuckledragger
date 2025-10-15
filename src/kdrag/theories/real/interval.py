import kdrag as kd
import kdrag.theories.real as R
import kdrag.smt as smt

"""
Interval arithmetic. Intervals are a record of hi and lo bounds.
"""
Interval = kd.Struct("Interval", ("lo", kd.R), ("hi", kd.R))
x, y, z = smt.Reals("x y z")
i, j, k, I, J, K = smt.Consts("i j k I J K", Interval)

setof = kd.define("setof", [i], smt.Lambda([x], smt.And(i.lo <= x, x <= i.hi)))

kd.notation.getitem.register(Interval, lambda a, idx: setof(a)[idx])

meet = kd.define("meet", [i, j], Interval.mk(R.max(i.lo, j.lo), R.min(i.hi, j.hi)))
meet_intersect = kd.prove(
    smt.ForAll([i, j], smt.SetIntersect(setof(i), setof(j)) == setof(meet(i, j))),
    by=[setof.defn, meet.defn, R.min.defn, R.max.defn],
)
kd.notation.and_.register(Interval, meet)

join = kd.define("join", [i, j], Interval.mk(R.min(i.lo, j.lo), R.max(i.hi, j.hi)))
join_union = kd.prove(
    smt.ForAll(
        [i, j], smt.IsSubset(smt.SetUnion(setof(i), setof(j)), setof(join(i, j)))
    ),
    by=[setof.defn, join.defn, R.min.defn, R.max.defn],
)
kd.notation.or_.register(Interval, join)

is_empty = kd.define("is_empty", [I], i.hi > i.lo)
empty = kd.define("empty", [], Interval.mk(smt.RealVal(1), smt.RealVal(0)))

width = kd.define("width", [i], i.hi - i.lo)
mid = kd.define("mid", [i], (i.lo + i.hi) / 2)

add = kd.notation.add.define([i, j], Interval.mk(i.lo + j.lo, i.hi + j.hi))
add_set = kd.prove(
    smt.ForAll(
        [x, y, i, j], smt.Implies(setof(i)[x] & setof(j)[y], setof(i + j)[x + y])
    ),
    by=[add.defn, setof.defn],
)

sub = kd.notation.sub.define([i, j], Interval.mk(i.lo - j.hi, i.hi - j.lo))


sub_set = kd.prove(
    kd.QForAll([x, y, i, j], i[x], j[y], (i - j)[x - y]),
    by=[sub.defn, setof.defn],
)


def Min(xs):
    assert len(xs) > 0
    if len(xs) == 1:
        return xs[0]
    else:
        rest = xs[1:]
        return smt.If(smt.And([xs[0] <= x for x in rest]), xs[0], Min(rest))


def Max(xs):
    assert len(xs) > 0
    if len(xs) == 1:
        return xs[0]
    else:
        rest = xs[1:]
        return smt.If(smt.And([xs[0] >= x for x in rest]), xs[0], Min(rest))


x, y, z = smt.Ints("x y z")

mul = kd.define(
    "mul",
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
