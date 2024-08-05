import z3
from z3 import ForAll, Function
from knuckledragger import lemma, axiom
import knuckledragger as kd

R = z3.RealSort()
RFun = z3.ArraySort(R, R)
RSeq = z3.ArraySort(z3.IntSort(), R)

x, y, z = z3.Reals("x y z")

plus = Function("plus", R, R, R)
plus_def = axiom(ForAll([x, y], plus(x, y) == x + y), "definition")

plus_0 = lemma(ForAll([x], plus(x, 0) == x), by=[plus_def])
plus_comm = lemma(ForAll([x, y], plus(x, y) == plus(y, x)), by=[plus_def])
plus_assoc = lemma(
    z3.ForAll([x, y, z], plus(x, plus(y, z)) == plus(plus(x, y), z)), by=[plus_def]
)

mul = Function("mul", R, R, R)
mul_def = axiom(ForAll([x, y], mul(x, y) == x * y), "definition")

mul_zero = lemma(ForAll([x], mul(x, 0) == 0), by=[mul_def])
mul_1 = lemma(ForAll([x], mul(x, 1) == x), by=[mul_def])
mul_comm = lemma(ForAll([x, y], mul(x, y) == mul(y, x)), by=[mul_def])
mul_assoc = lemma(
    ForAll([x, y, z], mul(x, mul(y, z)) == mul(mul(x, y), z)), by=[mul_def]
)
mul_distrib = lemma(
    ForAll([x, y, z], mul(x, plus(y, z)) == plus(mul(x, y), mul(x, z))),
    by=[mul_def, plus_def],
)


abs = kd.define("abs", [x], z3.If(x >= 0, x, -x))

abs_idem = kd.lemma(ForAll([x], abs(abs(x)) == abs(x)), by=[abs.defn])
abd_neg = kd.lemma(ForAll([x], abs(-x) == abs(x)), by=[abs.defn])
abs_ge_0 = kd.lemma(ForAll([x], abs(x) >= 0), by=[abs.defn])

nonneg = kd.define("nonneg", [x], abs(x) == x)
nonneg_ge_0 = kd.lemma(ForAll([x], nonneg(x) == (x >= 0)), by=[nonneg.defn, abs.defn])

max = kd.define("max", [x, y], z3.If(x >= y, x, y))
max_comm = kd.lemma(ForAll([x, y], max(x, y) == max(y, x)), by=[max.defn])
max_assoc = kd.lemma(
    ForAll([x, y, z], max(x, max(y, z)) == max(max(x, y), z)), by=[max.defn]
)
max_idem = kd.lemma(ForAll([x], max(x, x) == x), by=[max.defn])
max_ge = kd.lemma(ForAll([x, y], max(x, y) >= x), by=[max.defn])
max_ge_2 = kd.lemma(ForAll([x, y], max(x, y) >= y), by=[max.defn])

min = kd.define("min", [x, y], z3.If(x <= y, x, y))
min_comm = kd.lemma(ForAll([x, y], min(x, y) == min(y, x)), by=[min.defn])
min_assoc = kd.lemma(
    ForAll([x, y, z], min(x, min(y, z)) == min(min(x, y), z)), by=[min.defn]
)
min_idem = kd.lemma(ForAll([x], min(x, x) == x), by=[min.defn])
min_le = kd.lemma(ForAll([x, y], min(x, y) <= x), by=[min.defn])
min_le_2 = kd.lemma(ForAll([x, y], min(x, y) <= y), by=[min.defn])
