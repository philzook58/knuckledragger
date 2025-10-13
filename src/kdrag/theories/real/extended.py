import kdrag.smt as smt
import kdrag as kd
import kdrag.theories.set as set_

# https://en.wikipedia.org/wiki/Extended_real_number_line
# https://isabelle.in.tum.de/library/HOL/HOL-Library/Extended_Real.html

EReal = smt.Datatype("EReal")
EReal.declare("Real", ("val", smt.RealSort()))
EReal.declare("Inf")
EReal.declare("NegInf")
# EReal.declare("NaN")
EReal = EReal.create()

x, y, z = smt.Consts("x y z", EReal)

le = kd.notation.le.define(
    [x, y],
    kd.cond(
        (x == y, smt.BoolVal(True)),
        (x.is_NegInf, smt.BoolVal(True)),
        (y.is_Inf, smt.BoolVal(True)),
        (y.is_NegInf, smt.BoolVal(False)),
        (x.is_Inf, smt.BoolVal(False)),
        (smt.And(x.is_Real, y.is_Real), x.val <= y.val),
    ),
)

le_refl = kd.prove(kd.QForAll([x], x <= x), by=[le.defn])
le_trans = kd.prove(kd.QForAll([x, y, z], x <= y, y <= z, x <= z), by=[le.defn])
le_total = kd.prove(smt.ForAll([x, y], smt.Or(x <= y, y <= x)), by=[le.defn])

add_undef = smt.Function("add_undef", EReal, EReal, EReal)
add = kd.notation.add.define(
    [x, y],
    kd.cond(
        (smt.And(x.is_Real, y.is_Real), EReal.Real(x.val + y.val)),
        (smt.And(x.is_Inf, smt.Not(y.is_NegInf)), EReal.Inf),
        (smt.And(smt.Not(x.is_NegInf), y.is_Inf), EReal.Inf),
        (smt.And(x.is_NegInf, smt.Not(y.is_Inf)), EReal.NegInf),
        (smt.And(smt.Not(x.is_Inf), y.is_NegInf), EReal.NegInf),
        default=add_undef(x, y),
    ),
)
add_defined = kd.define(
    "add_defined",
    [x, y],
    smt.Or(
        smt.And(x.is_Real, y.is_Real),
        smt.And(x.is_Inf, smt.Not(y.is_NegInf)),
        smt.And(smt.Not(x.is_NegInf), y.is_Inf),
        smt.And(x.is_NegInf, smt.Not(y.is_Inf)),
        smt.And(smt.Not(x.is_Inf), y.is_NegInf),
    ),
)

defined_undef = kd.prove(
    kd.QForAll([x, y], smt.Not(add_defined(x, y)), x + y == add_undef(x, y)),
    by=[add_defined.defn, add.defn],
)

add_comm = kd.prove(
    kd.QForAll([x, y], add_defined(x, y), x + y == y + x),
    by=[add.defn, add_defined.defn],
)

add_comm1 = kd.prove(
    kd.QForAll([x, y], add_undef(x, y) == add_undef(y, x), x + y == y + x),
    by=[add.defn],
)

ERSet = set_.Set(EReal)
A = smt.Const("A", ERSet)
is_ub = kd.define("upper_bound", [A, x], kd.QForAll([y], A[y], y <= x))
is_lub = kd.define("is_lub", [A, x], is_ub(A, x) & kd.QForAll([y], is_ub(A, y), x <= y))
inf = smt.Function("lub", ERSet, EReal)
inf_ax = kd.axiom(smt.ForAll([A], is_lub(A, inf(A))))


EPosReal = smt.Datatype("EPosReal")
EPosReal.declare("real", ("val", smt.RealSort()))
EPosReal.declare("inf")
EPosReal = EPosReal.create()
x_p = smt.Const("x", EPosReal)
kd.notation.wf.define([x_p], smt.Implies(x_p.is_real, x_p.val >= 0))
