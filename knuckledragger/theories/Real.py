import z3
from z3 import ForAll, Function
from knuckledragger import lemma, axiom

R = z3.RealSort()
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

abs = Function("abs", R, R)
abs_def = axiom(ForAll([x], abs(x) == z3.If(x >= 0, x, -x)), "definition")

RFun = z3.ArraySort(R, R)
RSeq = z3.ArraySort(z3.IntSort(), R)
