import kdrag as kd
import kdrag.smt as smt

# import kdrag.theories.real as real
from kdrag.theories.real import R, RSet
from kdrag import axiom, prove
from kdrag.smt import ForAll, Const, Lambda, Implies, If, Or, Consts, And
from kdrag.theories.real.rset import closed_int

"""
Outer measure
https://en.wikipedia.org/wiki/Outer_measure
"""
omu = kd.kernel.declare("omu", RSet, R)
A, B = smt.Consts("A B", RSet)
omu_mono = axiom(ForAll([A, B], A <= B, omu(A) <= omu(B)), by="omu mono")
omu_subadd = axiom(
    ForAll([A, B], omu(A | B) <= omu(A) + omu(B)),
    by="omu subadd",
)  # Really countable subadditivity, but this is enough for now
x, y = smt.Reals("x y")
# To avoid issue with infinite measures, we restrict ourselves to unit interval
omu_interval = axiom(
    ForAll(
        [x, y],
        omu(closed_int(x, y)) == smt.If(x <= y, smt.If(y - x >= 1, 1, y - x), 0),
    ),
    by="omu interval",
)

# Theorem from empty set
omu_emp_zero = kd.axiom(omu(RSet.empty) == 0, by="omu empty")

# Option<Real> basically. But nice overloading
PosEReal0 = kd.Inductive("PosEReal0")
PosEReal0.declare("Inf")
PosEReal0.declare("Fin", ("fin", R))
PosEReal0 = PosEReal0.create()
x0 = Const("x0", PosEReal0)
PosEReal = Lambda(x0, Implies(x0.is_Fin, x0.fin >= 0))
x, y, z = Consts("x y z", PosEReal)


add = kd.notation.add.define(
    [x, y], If(Or(x.is_Inf, y.is_Inf), PosEReal0.Inf, PosEReal0.Fin(x.fin + y.fin))
)
add_comm = prove(ForAll([x, y], x + y == y + x), by=[add.defn])
add_assoc = prove(ForAll([x, y, z], (x + y) + z == x + (y + z)), by=[add.defn])
zero = PosEReal0.Fin(0)
add_zero = prove(ForAll([x], x + zero == x), by=[add.defn])
add_inf = prove(ForAll([x], x + PosEReal0.Inf == PosEReal0.Inf), by=[add.defn])

le = kd.notation.le.define(
    [x, y],
    If(y.is_Inf, smt.BoolVal(True), If(x.is_Inf, smt.BoolVal(False), x.fin <= y.fin)),
)
le_refl = prove(ForAll([x], x <= x), by=[le.defn])
le_antisym = prove(ForAll([x, y], x <= y, y <= x, x == y), by=[le.defn])
le_trans = prove(ForAll([x, y, z], x <= y, y <= z, x <= z), by=[le.defn])


def is_zero(x):
    return And(x.is_Fin, x.fin == 0)


# mul can kind of be defined
mul = kd.notation.mul.define(
    [x, y],
    If(Or(x.is_Inf, y.is_Inf), PosEReal0.Inf, PosEReal0.Fin(x.fin * y.fin)),
)
mul_comm = prove(ForAll([x, y], x * y == y * x), by=[mul.defn])
mul_assoc = prove(ForAll([x, y, z], (x * y) * z == x * (y * z)), by=[mul.defn])
mul_zero = prove(ForAll([x], x.is_Fin, x * zero == zero), by=[mul.defn])
mul_one = prove(
    ForAll([x], x * PosEReal0.Fin(1) == x), by=[mul.defn, add_zero, add_inf]
)
mul_inf = prove(
    ForAll([x], x * PosEReal0.Inf == PosEReal0.Inf),
    by=[mul.defn, add_inf],
)
