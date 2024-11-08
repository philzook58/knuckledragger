import kdrag as kd
import kdrag.theories.real as R
import kdrag.smt as smt

"""
Interval arithmetic. Intervals are a record of hi and lo bounds.
"""
Interval = kd.notation.Record("Interval", ("lo", kd.R), ("hi", kd.R))
x, y, z = smt.Reals("x y z")
i, j, k = smt.Consts("i j k", Interval)

setof = kd.define("setof", [i], smt.Lambda([x], smt.And(i.lo <= x, x <= i.hi)))

meet = kd.define("meet", [i, j], Interval.mk(R.max(i.lo, j.lo), R.min(i.hi, j.hi)))
meet_intersect = kd.lemma(
    smt.ForAll([i, j], smt.SetIntersect(setof(i), setof(j)) == setof(meet(i, j))),
    by=[setof.defn, meet.defn, R.min.defn, R.max.defn],
)

join = kd.define("join", [i, j], Interval.mk(R.min(i.lo, j.lo), R.max(i.hi, j.hi)))
join_union = kd.lemma(
    smt.ForAll(
        [i, j], smt.IsSubset(smt.SetUnion(setof(i), setof(j)), setof(join(i, j)))
    ),
    by=[setof.defn, join.defn, R.min.defn, R.max.defn],
)


width = kd.define("width", [i], i.hi - i.lo)
mid = kd.define("mid", [i], (i.lo + i.hi) / 2)

add = kd.notation.add.define([i, j], Interval.mk(i.lo + j.lo, i.hi + j.hi))
add_set = kd.lemma(
    smt.ForAll(
        [x, y, i, j], smt.Implies(setof(i)[x] & setof(j)[y], setof(i + j)[x + y])
    ),
    by=[add.defn, setof.defn],
)

sub = kd.notation.sub.define([i, j], Interval.mk(i.lo - j.hi, i.hi - j.lo))
