import kdrag.smt as smt
from kdrag.smt import ForAll, Function
from kdrag import lemma, axiom
import kdrag as kd

R = smt.RealSort()
RFun = smt.ArraySort(R, R)
RSeq = smt.ArraySort(smt.IntSort(), R)

x, y, z = smt.Reals("x y z")

f, g = smt.Consts("f g", RFun)
kd.notation.add.define([f, g], smt.Lambda([x], f[x] + g[x]))
kd.notation.sub.define([f, g], smt.Lambda([x], f[x] - g[x]))
kd.notation.mul.define([f, g], smt.Lambda([x], f[x] * g[x]))
kd.notation.div.define([f, g], smt.Lambda([x], f[x] / g[x]))


plus = Function("plus", R, R, R)
plus_def = axiom(ForAll([x, y], plus(x, y) == x + y), "definition")

plus_0 = lemma(ForAll([x], plus(x, 0) == x), by=[plus_def])
plus_comm = lemma(ForAll([x, y], plus(x, y) == plus(y, x)), by=[plus_def])
plus_assoc = lemma(
    smt.ForAll([x, y, z], plus(x, plus(y, z)) == plus(plus(x, y), z)), by=[plus_def]
)

mul = Function("mul", R, R, R)
mul_def = axiom(ForAll([x, y], mul(x, y) == x * y), "definition")

mul_zero = lemma(ForAll([x], mul(x, 0) == 0), by=[mul_def])
mul_1 = lemma(ForAll([x], mul(x, 1) == x), by=[mul_def])
mul_comm = lemma(ForAll([x, y], mul(x, y) == mul(y, x)), by=[mul_def])
mul_assoc = lemma(
    ForAll([x, y, z], mul(x, mul(y, z)) == mul(mul(x, y), z)), by=[mul_def], admit=True
)
mul_distrib = lemma(
    ForAll([x, y, z], mul(x, plus(y, z)) == plus(mul(x, y), mul(x, z))),
    by=[mul_def, plus_def],
)


abs = kd.define("absR", [x], smt.If(x >= 0, x, -x))
sgn = kd.define("sgn", [x], smt.If(x > 0, 1, smt.If(x < 0, -1, 0)))

sgn_abs = kd.lemma(ForAll([x], x == abs(x) * sgn(x)), by=[abs.defn, sgn.defn])

abs_idem = kd.lemma(ForAll([x], abs(abs(x)) == abs(x)), by=[abs.defn])
abs_neg = kd.lemma(ForAll([x], abs(-x) == abs(x)), by=[abs.defn])
abs_ge_0 = kd.lemma(ForAll([x], abs(x) >= 0), by=[abs.defn])

nonneg = kd.define("nonneg", [x], abs(x) == x)
nonneg_ge_0 = kd.lemma(ForAll([x], nonneg(x) == (x >= 0)), by=[nonneg.defn, abs.defn])

max = kd.define("max", [x, y], smt.If(x >= y, x, y))
max_comm = kd.lemma(ForAll([x, y], max(x, y) == max(y, x)), by=[max.defn])
max_assoc = kd.lemma(
    ForAll([x, y, z], max(x, max(y, z)) == max(max(x, y), z)), by=[max.defn]
)
max_idem = kd.lemma(ForAll([x], max(x, x) == x), by=[max.defn])
max_ge = kd.lemma(ForAll([x, y], max(x, y) >= x), by=[max.defn])
max_ge_2 = kd.lemma(ForAll([x, y], max(x, y) >= y), by=[max.defn])

min = kd.define("min", [x, y], smt.If(x <= y, x, y))
min_comm = kd.lemma(ForAll([x, y], min(x, y) == min(y, x)), by=[min.defn])
min_assoc = kd.lemma(
    ForAll([x, y, z], min(x, min(y, z)) == min(min(x, y), z)), by=[min.defn]
)
min_idem = kd.lemma(ForAll([x], min(x, x) == x), by=[min.defn])
min_le = kd.lemma(ForAll([x, y], min(x, y) <= x), by=[min.defn])
min_le_2 = kd.lemma(ForAll([x, y], min(x, y) <= y), by=[min.defn])


pow = kd.define("pow", [x, y], x**y)
pow_add = kd.axiom(
    kd.QForAll([x, y, z], x >= 0, pow(x, y + z) == pow(x, y) * pow(x, z))
)
pow_one = kd.lemma(kd.QForAll([x], pow(x, 1) == x), by=[pow.defn])
# pow_zero = kd.kernel.lemma(kd.QForAll([x], x > 0, pow(x, 0) == 1), by=[pow.defn])
kd.kernel.lemma(smt.Implies(x > 0, x**0 == 1))
# pow_pos = kd.lemma(kd.QForAll([x, y], x > 0, pow(x, y) > 0), by=[pow.defn])

# Inverses
sqrt = kd.define("sqrt", [x], pow(x, 0.5))
sqrt_define = kd.lemma(smt.ForAll([x], sqrt(x) == x**0.5), by=[sqrt.defn, pow.defn])
_1 = kd.kernel.lemma(smt.Implies(x >= 0, (x**0.5) ** 2 == x))  # forall messes it up?
sqrt_square = kd.lemma(
    kd.QForAll([x], x >= 0, sqrt(x) ** 2 == x),
    by=[sqrt_define, sqrt.defn, _1],
    admit=True,
)

exp = smt.Function("exp", kd.R, kd.R)
exp_add = kd.axiom(smt.ForAll([x, y], exp(x + y) == exp(x) * exp(y)))
exp_lower = kd.axiom(
    smt.ForAll([x], exp(x) >= 1 + x)
)  # tight low approximation at x = 0.
exp_pos = kd.axiom(smt.ForAll([x], exp(x) > 0))  # maybe we can derive this one?

exp_zero = kd.lemma(smt.ForAll([x], exp(0) == 1), by=[exp_add, exp_pos])

exp_div = kd.lemma(smt.ForAll([x, y], exp(x) * exp(-x) == 1), by=[exp_add, exp_zero])
exp_nzero = kd.lemma(smt.ForAll([x], exp(x) != 0), by=[exp_div])
exp_inv = kd.lemma(smt.ForAll([x], exp(-x) == 1 / exp(x)), by=[exp_div])


floor = kd.define("floor", [x], smt.ToReal(smt.ToInt(x)))
n = smt.Int("n")
int_real_galois_lt = kd.lemma(ForAll([x, n], (x < smt.ToReal(n)) == (smt.ToInt(x) < n)))
int_real_galois_le = kd.lemma(
    ForAll([x, n], (smt.ToReal(n) <= x) == (n <= smt.ToInt(x)))
)

_2 = kd.lemma(ForAll([x], smt.ToInt(floor(x)) == smt.ToInt(x)), by=[floor.defn])
floor_idem = kd.lemma(ForAll([x], floor(floor(x)) == floor(x)), by=[floor.defn, _2])
floor_le = kd.lemma(ForAll([x], floor(x) <= x), by=[floor.defn])
floor_gt = kd.lemma(ForAll([x], x < floor(x) + 1), by=[floor.defn])

c = kd.Calc([n, x], smt.ToReal(n) <= x)
c.eq(n <= smt.ToInt(x))
c.eq(smt.ToReal(n) <= floor(x), by=[floor.defn])
floor_minint = c.qed(defns=False)


EReal = smt.Datatype("EReal")
EReal.declare("real", ("val", smt.RealSort()))
EReal.declare("inf")
EReal.declare("neg_inf")
EReal.declare("NaN")
EReal = EReal.create()
