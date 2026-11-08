from kdrag.smt import (
    And,
    BoolVal,
    Const,
    Consts,
    Datatype,
    ForAll,
    Function,
    Implies,
    Not,
    Or,
    RealSort,
)
import kdrag as kd
from kdrag import QForAll, axiom, cond, define, prove
import kdrag.theories.set as set_

# https://en.wikipedia.org/wiki/Extended_real_number_line
# https://isabelle.in.tum.de/library/HOL/HOL-Library/Extended_Real.html

EReal = Datatype("EReal")
EReal.declare("Real", ("val", RealSort()))
EReal.declare("Inf")
EReal.declare("NegInf")
# EReal.declare("NaN")
EReal = EReal.create()

x, y, z = Consts("x y z", EReal)

le = kd.notation.le.define(
    [x, y],
    cond(
        (x == y, BoolVal(True)),
        (x.is_NegInf, BoolVal(True)),
        (y.is_Inf, BoolVal(True)),
        (y.is_NegInf, BoolVal(False)),
        (x.is_Inf, BoolVal(False)),
        (And(x.is_Real, y.is_Real), x.val <= y.val),
    ),
)

le_refl = prove(QForAll([x], x <= x), by=[le.defn])
le_trans = prove(QForAll([x, y, z], x <= y, y <= z, x <= z), by=[le.defn])
le_total = prove(ForAll([x, y], Or(x <= y, y <= x)), by=[le.defn])

add_undef = Function("add_undef", EReal, EReal, EReal)
add = kd.notation.add.define(
    [x, y],
    cond(
        (And(x.is_Real, y.is_Real), EReal.Real(x.val + y.val)),
        (And(x.is_Inf, Not(y.is_NegInf)), EReal.Inf),
        (And(Not(x.is_NegInf), y.is_Inf), EReal.Inf),
        (And(x.is_NegInf, Not(y.is_Inf)), EReal.NegInf),
        (And(Not(x.is_Inf), y.is_NegInf), EReal.NegInf),
        default=add_undef(x, y),
    ),
)
add_defined = define(
    "add_defined",
    [x, y],
    Or(
        And(x.is_Real, y.is_Real),
        And(x.is_Inf, Not(y.is_NegInf)),
        And(Not(x.is_NegInf), y.is_Inf),
        And(x.is_NegInf, Not(y.is_Inf)),
        And(Not(x.is_Inf), y.is_NegInf),
    ),
)

defined_undef = prove(
    QForAll([x, y], Not(add_defined(x, y)), x + y == add_undef(x, y)),
    by=[add_defined.defn, add.defn],
)

add_comm = prove(
    QForAll([x, y], add_defined(x, y), x + y == y + x),
    by=[add.defn, add_defined.defn],
)

add_comm1 = prove(
    QForAll([x, y], add_undef(x, y) == add_undef(y, x), x + y == y + x),
    by=[add.defn],
)

ERSet = set_.Set(EReal)
A = Const("A", ERSet)
is_ub = define("upper_bound", [A, x], QForAll([y], A[y], y <= x))
is_lub = define("is_lub", [A, x], is_ub(A, x) & QForAll([y], is_ub(A, y), x <= y))
inf = Function("lub", ERSet, EReal)
inf_ax = axiom(ForAll([A], is_lub(A, inf(A))))


EPosReal = Datatype("EPosReal")
EPosReal.declare("real", ("val", RealSort()))
EPosReal.declare("inf")
EPosReal = EPosReal.create()
x_p = Const("x", EPosReal)
kd.notation.wf.define([x_p], Implies(x_p.is_real, x_p.val >= 0))
