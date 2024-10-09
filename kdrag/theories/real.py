import kdrag.smt as smt
from kdrag.smt import ForAll, Function
from kdrag import lemma, axiom
import kdrag as kd

R = smt.RealSort()
RFun = smt.ArraySort(R, R)
RSeq = smt.ArraySort(smt.IntSort(), R)

x, y, z = smt.Reals("x y z")

f, g = smt.Consts("f g", RFun)
fadd = kd.notation.add.define([f, g], smt.Lambda([x], f[x] + g[x]))
fsub = kd.notation.sub.define([f, g], smt.Lambda([x], f[x] - g[x]))
fmul = kd.notation.mul.define([f, g], smt.Lambda([x], f[x] * g[x]))
fdiv = kd.notation.div.define([f, g], smt.Lambda([x], f[x] / g[x]))

poly = smt.Function("poly", RFun, smt.BoolSort())
kd.axiom(ForAll([x], poly(smt.K(smt.RealSort(), x))))
kd.axiom(poly(smt.Lambda([x], x)))
kd.axiom(kd.QForAll([f, g], poly(f), poly(g), poly(f + g)))
kd.axiom(kd.QForAll([f, g], poly(f), poly(g), poly(f * g)))


# NReal = kd.NewType("NReal", R)


add = kd.define("add", [x, y], x + y)

add_0 = lemma(ForAll([x], add(x, 0) == x), by=[add.defn])
add_comm = lemma(ForAll([x, y], add(x, y) == add(y, x)), by=[add.defn])
add_assoc = lemma(
    smt.ForAll([x, y, z], add(x, add(y, z)) == add(add(x, y), z)), by=[add.defn]
)

sub = kd.define("sub", [x, y], x - y)
sub_0 = lemma(ForAll([x], sub(x, 0) == x), by=[sub.defn])
sub_add = lemma(
    ForAll([x, y, z], (add(x, y) == z) == (x == sub(z, y))), by=[sub.defn, add.defn]
)

mul = kd.define("mul", [x, y], x * y)
mul_zero = lemma(ForAll([x], mul(x, 0) == 0), by=[mul.defn])
mul_1 = lemma(ForAll([x], mul(x, 1) == x), by=[mul.defn])
mul_comm = lemma(ForAll([x, y], mul(x, y) == mul(y, x)), by=[mul.defn])
mul_assoc = lemma(
    ForAll([x, y, z], mul(x, mul(y, z)) == mul(mul(x, y), z)), by=[mul.defn], admit=True
)
mul_distrib = lemma(
    ForAll([x, y, z], mul(x, add(y, z)) == add(mul(x, y), mul(x, z))),
    by=[mul.defn, add.defn],
)


def abstract_arith(t: smt.ExprRef) -> smt.ExprRef:
    """
    Z3 has difficult ematching over arithmetic expressions.
    Abstracting them to uninterpreted functions can help.
    """
    if smt.is_var(t):
        return t
    if smt.is_app(t):
        if t.decl() == (x + y).decl():
            return add(abstract_arith(t.arg(0)), abstract_arith(t.arg(1)))
        elif t.decl() == (x - y).decl():
            return sub(abstract_arith(t.arg(0)), abstract_arith(t.arg(1)))
        elif t.decl() == (x * y).decl():
            return mul(abstract_arith(t.arg(0)), abstract_arith(t.arg(1)))
        else:
            f = t.decl()
            return f(*[abstract_arith(c) for c in t.children()])


abs = kd.define("absR", [x], smt.If(x >= 0, x, -x))
sgn = kd.define("sgn", [x], smt.If(x > 0, 1, smt.If(x < 0, -1, 0)))

sgn_abs = kd.lemma(ForAll([x], x == abs(x) * sgn(x)), by=[abs.defn, sgn.defn])
abs_le = kd.lemma(
    ForAll([x, y], (abs(x) <= y) == smt.And(-y <= x, x <= y)), by=[abs.defn]
)
abs_idem = kd.lemma(ForAll([x], abs(abs(x)) == abs(x)), by=[abs.defn])
abs_neg = kd.lemma(ForAll([x], abs(-x) == abs(x)), by=[abs.defn])
abs_pos = kd.lemma(ForAll([x], abs(x) >= 0), by=[abs.defn])
abs_add = kd.lemma(ForAll([x, y], abs(x + y) <= abs(x) + abs(y)), by=[abs.defn])
abs_mul = kd.lemma(ForAll([x, y], abs(x * y) == abs(x) * abs(y)), by=[abs.defn])
abs_triangle = kd.lemma(
    ForAll([x, y, z], abs(x - y) <= abs(x - z) + abs(z - y)), by=[abs.defn]
)


nonneg = kd.define("nonneg", [x], abs(x) == x)
nonneg_ge_0 = kd.lemma(ForAll([x], nonneg(x) == (x >= 0)), by=[nonneg.defn, abs.defn])

max = kd.define("max", [x, y], smt.If(x >= y, x, y))
max_le = kd.lemma(ForAll([x, y], (x <= y) == (max(x, y) == y)), by=[max.defn])
max_comm = kd.lemma(ForAll([x, y], max(x, y) == max(y, x)), by=[max.defn])
max_assoc = kd.lemma(
    ForAll([x, y, z], max(x, max(y, z)) == max(max(x, y), z)), by=[max.defn]
)
max_idem = kd.lemma(ForAll([x], max(x, x) == x), by=[max.defn])
max_ge = kd.lemma(ForAll([x, y], max(x, y) >= x), by=[max.defn])
max_ge_2 = kd.lemma(ForAll([x, y], max(x, y) >= y), by=[max.defn])

min = kd.define("min", [x, y], smt.If(x <= y, x, y))
min_le = kd.lemma(ForAll([x, y], (x <= y) == (min(x, y) == x)), by=[min.defn])
min_comm = kd.lemma(ForAll([x, y], min(x, y) == min(y, x)), by=[min.defn])
min_assoc = kd.lemma(
    ForAll([x, y, z], min(x, min(y, z)) == min(min(x, y), z)), by=[min.defn]
)
min_idem = kd.lemma(ForAll([x], min(x, x) == x), by=[min.defn])
min_le_2 = kd.lemma(ForAll([x, y], min(x, y) <= x), by=[min.defn])
min_le_3 = kd.lemma(ForAll([x, y], min(x, y) <= y), by=[min.defn])


n, m = smt.Ints("n m")
to_real_add = kd.lemma(
    ForAll([n, m], smt.ToReal(n + m) == smt.ToReal(n) + smt.ToReal(m))
)
to_real_sub = kd.lemma(
    ForAll([n, m], smt.ToReal(n - m) == smt.ToReal(n) - smt.ToReal(m))
)
to_real_mul = kd.lemma(
    ForAll([n, m], smt.ToReal(n * m) == smt.ToReal(n) * smt.ToReal(m))
)
to_real_neg = kd.lemma(ForAll([n], smt.ToReal(-n) == -smt.ToReal(n)))
to_real_inj = kd.lemma(ForAll([n, m], (smt.ToReal(n) == smt.ToReal(m)) == (n == m)))
to_real_mono = kd.lemma(ForAll([n, m], (n < m) == (smt.ToReal(n) < smt.ToReal(m))))

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


pow = kd.define("pow", [x, y], x**y)
pow_add = kd.axiom(
    kd.QForAll([x, y, z], x >= 0, pow(x, y + z) == pow(x, y) * pow(x, z))
)
pow_one = kd.lemma(kd.QForAll([x], pow(x, 1) == x), by=[pow.defn])
pow_two = kd.lemma(kd.QForAll([x], pow(x, 2) == x * x), by=[pow.defn])
pow_three = kd.lemma(kd.QForAll([x], pow(x, 3) == x * x * x), by=[pow.defn])
# pow_zero = kd.kernel.lemma(kd.QForAll([x], x > 0, pow(x, 0) == 1), by=[pow.defn])
kd.kernel.lemma(smt.Implies(x > 0, x**0 == 1))
# pow_pos = kd.lemma(kd.QForAll([x, y], x > 0, pow(x, y) > 0), by=[pow.defn])

sqr = kd.define("sqr", [x], x * x)


sqrt = kd.define("sqrt", [x], x**0.5)
_1 = kd.kernel.lemma(smt.Implies(x >= 0, x**0.5 >= 0))
sqrt_pos = kd.lemma(kd.QForAll([x], x >= 0, sqrt(x) >= 0), by=[_1], admit=True)
sqrt_define = kd.lemma(smt.ForAll([x], sqrt(x) == x**0.5), by=[sqrt.defn, pow.defn])
_1 = kd.kernel.lemma(smt.Implies(x >= 0, (x**0.5) ** 2 == x))  # forall messes it up?
sqrt_square = kd.lemma(
    kd.QForAll([x], x >= 0, sqrt(x) ** 2 == x),
    by=[sqrt_define, sqrt.defn, _1],
    admit=True,
)
sqr_sqrt = kd.lemma(
    kd.QForAll([x], x >= 0, sqr(sqrt(x)) == x), by=[sqrt_square, sqr.defn]
)
_1 = kd.kernel.lemma(smt.Implies(x >= 0, (x**2) ** 0.5 == x))
sqrt_sqr = kd.lemma(kd.QForAll([x], x >= 0, sqrt(sqr(x)) == x), by=[_1], admit=True)


exp = smt.Const("exp", kd.R >> kd.R)
exp_add = kd.axiom(smt.ForAll([x, y], exp(x + y) == exp(x) * exp(y)))
exp_lower = kd.axiom(
    smt.ForAll([x], exp(x) >= 1 + x)
)  # tight low approximation at x = 0.
exp_pos = kd.axiom(smt.ForAll([x], exp(x) > 0))  # maybe we can derive this one?

exp_zero = kd.lemma(smt.ForAll([x], exp(0) == 1), by=[exp_add, exp_pos])

exp_div = kd.lemma(smt.ForAll([x, y], exp(x) * exp(-x) == 1), by=[exp_add, exp_zero])
exp_nzero = kd.lemma(smt.ForAll([x], exp(x) != 0), by=[exp_div])
exp_inv = kd.lemma(smt.ForAll([x], exp(-x) == 1 / exp(x)), by=[exp_div])


ln = smt.Function("ln", kd.R, kd.R)
ln_exp = kd.axiom(smt.ForAll([x], ln(exp(x)) == x))
# TODO. some of these are redundant depending on the range of ln being R.
ln_mul = kd.axiom(kd.QForAll([x, y], x > 0, y > 0, ln(x * y) == ln(x) + ln(y)))
ln_one = kd.lemma(smt.ForAll([x], ln(1) == 0), by=[ln_exp, exp_zero])

exp_ln = kd.axiom(kd.QForAll([x], x > 0, exp(ln(x)) == x))


cos = smt.Const("cos", kd.R >> kd.R)
sin = smt.Const("sin", kd.R >> kd.R)

pythag = kd.axiom(smt.ForAll([x], cos(x) ** 2 + sin(x) ** 2 == 1))
cos_abs_le = kd.lemma(smt.ForAll([x], abs(cos(x)) <= 1), by=[pythag, abs.defn])
sin_abs_le = kd.lemma(smt.ForAll([x], abs(sin(x)) <= 1), by=[pythag, abs.defn])

cos_0 = kd.axiom(cos(0) == 1)
sin_0 = kd.lemma(sin(0) == 0, by=[pythag, cos_0])

pi = smt.Const("pi", kd.R)
pi_bnd = kd.axiom(smt.And(3.14159 < pi, pi < 3.14160))

cos_pi = kd.axiom(cos(pi) == -1)
sin_pi = kd.lemma(sin(pi) == 0, by=[pythag, cos_pi])

cos_neg = kd.axiom(smt.ForAll([x], cos(-x) == cos(x)))
sin_neg = kd.axiom(smt.ForAll([x], sin(-x) == -sin(x)))

cos_add = kd.axiom(smt.ForAll([x, y], cos(x + y) == cos(x) * cos(y) - sin(x) * sin(y)))
sin_add = kd.axiom(smt.ForAll([x, y], sin(x + y) == sin(x) * cos(y) + cos(x) * sin(y)))


EReal = smt.Datatype("EReal")
EReal.declare("real", ("val", smt.RealSort()))
EReal.declare("inf")
EReal.declare("neg_inf")
EReal.declare("NaN")
EReal = EReal.create()

EPosReal = smt.Datatype("EPosReal")
EPosReal.declare("real", ("val", smt.RealSort()))
EPosReal.declare("inf")
EPosReal = EPosReal.create()
x_p = smt.Const("x", EPosReal)
kd.notation.wf.define([x_p], smt.Implies(x_p.is_real, x_p.val >= 0))

ident = kd.define("ident", [], smt.Lambda([x], x))
const = kd.define("const", [x], smt.K(smt.RealSort(), x))
X = ident

# Since not all functions are differentiable, the connection of deriv to the analytic definition of derivative is a proof obligation
deriv = smt.Function("deriv", RFun, RFun)
deriv_const = kd.axiom(ForAll([x], deriv(const(x)) == const(0)))
deriv_ident = kd.axiom(deriv(X) == const(1))
deriv_sin = kd.axiom(deriv(sin) == cos)
deriv_cos = kd.axiom(deriv(smt.Lambda([x], cos(x))) == smt.Lambda([x], -sin(x)))
deriv_exp = kd.axiom(deriv(exp) == exp)
deriv_add = kd.axiom(ForAll([f, g], deriv(f + g) == deriv(f) + deriv(g)))
deriv_mul = kd.axiom(ForAll([f, g], deriv(f * g) == deriv(f) * g + f * deriv(g)))
