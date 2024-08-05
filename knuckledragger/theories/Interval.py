import knuckledragger as kd
import knuckledragger.theories.Real as R
import z3

Interval = kd.notation.Record("Interval", ("lo", kd.R), ("hi", kd.R))
x, y, z = z3.Reals("x y z")
i, j, k = z3.Consts("i j k", Interval)

setof = kd.define("setof", [i], z3.Lambda([x], z3.And(i.lo <= x, x <= i.hi)))

meet = kd.define("meet", [i, j], Interval.mk(R.max(i.lo, j.lo), R.min(i.hi, j.hi)))
meet_intersect = kd.lemma(
    z3.ForAll([i, j], z3.SetIntersect(setof(i), setof(j)) == setof(meet(i, j))),
    by=[setof.defn, meet.defn, R.min.defn, R.max.defn],
)

join = kd.define("join", [i, j], Interval.mk(R.min(i.lo, j.lo), R.max(i.hi, j.hi)))
join_union = kd.lemma(
    z3.ForAll([i, j], z3.IsSubset(z3.SetUnion(setof(i), setof(j)), setof(join(i, j)))),
    by=[setof.defn, join.defn, R.min.defn, R.max.defn],
)


width = kd.define("width", [i], i.hi - i.lo)
mid = kd.define("mid", [i], (i.lo + i.hi) / 2)

add = kd.notation.add.define([i, j], Interval.mk(i.lo + j.lo, i.hi + j.hi))
add_set = kd.lemma(
    z3.ForAll([x, y, i, j], z3.Implies(setof(i)[x] & setof(j)[y], setof(i + j)[x + y])),
    by=[add.defn, setof.defn],
)

sub = kd.notation.sub.define([i, j], Interval.mk(i.lo - j.hi, i.hi - j.lo))
