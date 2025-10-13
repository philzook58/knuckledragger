"""
Definitions about the reals.

Transcendental functions and bounds.
"""

import kdrag.smt as smt
import kdrag.theories.set as set_
from kdrag.smt import ForAll
import kdrag as kd
import kdrag.property as prop

T = smt.RealSort()

R = smt.RealSort()
RFun = smt.ArraySort(R, R)
RSeq = smt.ArraySort(smt.IntSort(), R)
RSet = set_.Set(R)
S = RSet.full

real_db = []
real_simp = []


def rlemma(thm, by=[], **kwargs):
    return kd.prove(thm, by + real_db + real_simp, **kwargs)


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

zero = kd.define("zero", [], smt.RealVal(0))


add = kd.define("add", [x, y], x + y)

add_0 = kd.prove(ForAll([x], add(x, 0) == x), by=[add.defn])
add_comm = kd.prove(ForAll([x, y], add(x, y) == add(y, x)), by=[add.defn])
add_assoc = kd.prove(
    smt.ForAll([x, y, z], add(x, add(y, z)) == add(add(x, y), z)), by=[add.defn]
)


class Add:
    f = add
    comm = add_comm
    assoc = add_assoc
    e = smt.RealVal(0)
    left_id = kd.prove(ForAll([x], add(0, x) == x), by=[add.defn])
    right_id = kd.prove(ForAll([x], add(x, 0) == x), by=[add.defn])


AddComm: type[prop.Comm] = Add
AddAssoc: type[prop.Assoc] = Add
AddId: type[prop.Identity] = Add

sub = kd.define("sub", [x, y], x - y)
sub_0 = kd.prove(ForAll([x], sub(x, 0) == x), by=[sub.defn])
sub_add = kd.prove(
    ForAll([x, y, z], (add(x, y) == z) == (x == sub(z, y))), by=[sub.defn, add.defn]
)

mul = kd.define("mul", [x, y], x * y)
mul_zero = kd.prove(ForAll([x], mul(x, 0) == 0), by=[mul.defn])
one = kd.define("one", [], smt.RealVal(1))
mul_one = kd.prove(ForAll([x], mul(x, one) == x), by=[mul.defn, one.defn])
one_mul = kd.prove(ForAll([x], mul(one, x) == x), by=[mul.defn, one.defn])
mul_comm = kd.prove(ForAll([x, y], mul(x, y) == mul(y, x)), by=[mul.defn])
# mul_assoc = kd.prove(
#    ForAll([x, y, z], mul(x, mul(y, z)) == mul(mul(x, y), z)), by=[mul.defn]
# )
_l = kd.Lemma(smt.ForAll([x, y, z], mul(x, mul(y, z)) == mul(mul(x, y), z)))
_x, _y, _z = _l.fixes()
_l.unfold()
_l.auto()
mul_assoc = _l.qed()


class Mul:
    f = mul
    comm = mul_comm
    assoc = mul_assoc
    e = smt.RealVal(1)
    left_id = kd.prove(ForAll([x], mul(1, x) == x), by=[mul.defn])
    right_id = kd.prove(ForAll([x], mul(x, 1) == x), by=[mul.defn])


MulAssoc: type[prop.Assoc] = Mul

mul_distrib = kd.prove(
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
    elif smt.is_app(t):
        if t.decl() == (x + y).decl():
            return add(abstract_arith(t.arg(0)), abstract_arith(t.arg(1)))
        elif t.decl() == (x - y).decl():
            return sub(abstract_arith(t.arg(0)), abstract_arith(t.arg(1)))
        elif t.decl() == (x * y).decl():
            return mul(abstract_arith(t.arg(0)), abstract_arith(t.arg(1)))
        else:
            f = t.decl()
            return f(*[abstract_arith(c) for c in t.children()])
    else:
        raise Exception("unimplemented case in abstract_arith", t)


abs = kd.define("absR", [x], smt.If(x >= 0, x, -x))
sgn = kd.define("sgn", [x], smt.If(x > 0, 1, smt.If(x < 0, -1, 0)))

sgn_abs = kd.prove(ForAll([x], abs(x) * sgn(x) == x), by=[abs.defn, sgn.defn])
abs_le = kd.prove(
    ForAll([x, y], (abs(x) <= y) == smt.And(-y <= x, x <= y)), by=[abs.defn]
)
abs_idem = kd.prove(ForAll([x], abs(abs(x)) == abs(x)), by=[abs.defn])
abs_neg = kd.prove(ForAll([x], abs(-x) == abs(x)), by=[abs.defn])
abs_pos = kd.prove(ForAll([x], abs(x) >= 0), by=[abs.defn])
abs_add = kd.prove(ForAll([x, y], abs(x + y) <= abs(x) + abs(y)), by=[abs.defn])
abs_mul = kd.prove(ForAll([x, y], abs(x * y) == abs(x) * abs(y)), by=[abs.defn])
abs_triangle = kd.prove(
    ForAll([x, y, z], abs(x - y) <= abs(x - z) + abs(z - y)), by=[abs.defn]
)


nonneg = kd.define("nonneg", [x], abs(x) == x)
nonneg_ge_0 = kd.prove(ForAll([x], nonneg(x) == (x >= 0)), by=[nonneg.defn, abs.defn])

max = kd.define("max", [x, y], smt.If(x >= y, x, y))
max_le = kd.prove(ForAll([x, y], (x <= y) == (max(x, y) == y)), by=[max.defn])
max_comm = kd.prove(ForAll([x, y], max(x, y) == max(y, x)), by=[max.defn])
max_assoc = kd.prove(
    ForAll([x, y, z], max(x, max(y, z)) == max(max(x, y), z)), by=[max.defn]
)
max_idem = kd.prove(ForAll([x], max(x, x) == x), by=[max.defn])
max_ge = kd.prove(ForAll([x, y], max(x, y) >= x), by=[max.defn])
max_ge_2 = kd.prove(ForAll([x, y], max(x, y) >= y), by=[max.defn])

min = kd.define("min", [x, y], smt.If(x <= y, x, y))
min_le = kd.prove(ForAll([x, y], (x <= y) == (min(x, y) == x)), by=[min.defn])
min_comm = kd.prove(ForAll([x, y], min(x, y) == min(y, x)), by=[min.defn])
min_assoc = kd.prove(
    ForAll([x, y, z], min(x, min(y, z)) == min(min(x, y), z)), by=[min.defn]
)
min_idem = kd.prove(ForAll([x], min(x, x) == x), by=[min.defn])
min_le_2 = kd.prove(ForAll([x, y], min(x, y) <= x), by=[min.defn])
min_le_3 = kd.prove(ForAll([x, y], min(x, y) <= y), by=[min.defn])


n, m = smt.Ints("n m")
to_real_add = kd.prove(
    ForAll([n, m], smt.ToReal(n + m) == smt.ToReal(n) + smt.ToReal(m))
)
to_real_sub = kd.prove(
    ForAll([n, m], smt.ToReal(n - m) == smt.ToReal(n) - smt.ToReal(m))
)
to_real_mul = kd.prove(
    ForAll([n, m], smt.ToReal(n * m) == smt.ToReal(n) * smt.ToReal(m))
)
to_real_neg = kd.prove(ForAll([n], smt.ToReal(-n) == -smt.ToReal(n)))
to_real_inj = kd.prove(ForAll([n, m], (smt.ToReal(n) == smt.ToReal(m)) == (n == m)))
to_real_mono = kd.prove(ForAll([n, m], (n < m) == (smt.ToReal(n) < smt.ToReal(m))))

floor = kd.define("floor", [x], smt.ToReal(smt.ToInt(x)))
n = smt.Int("n")
int_real_galois_lt = kd.prove(ForAll([x, n], (x < smt.ToReal(n)) == (smt.ToInt(x) < n)))
int_real_galois_le = kd.prove(
    ForAll([x, n], (smt.ToReal(n) <= x) == (n <= smt.ToInt(x)))
)

_2 = kd.prove(ForAll([x], smt.ToInt(floor(x)) == smt.ToInt(x)), by=[floor.defn])
floor_idem = kd.prove(ForAll([x], floor(floor(x)) == floor(x)), by=[floor.defn, _2])
floor_le = kd.prove(ForAll([x], floor(x) <= x), by=[floor.defn])
floor_gt = kd.prove(ForAll([x], x < floor(x) + 1), by=[floor.defn])

# c = kd.Calc([n, x], smt.ToReal(n) <= x)
# c.eq(n <= smt.ToInt(x))
# c.eq(smt.ToReal(n) <= floor(x), by=[floor.defn])
# floor_minint = c.qed(defns=False)


pow = kd.define("pow", [x, y], x**y)
pow_add = kd.axiom(
    kd.QForAll([x, y, z], x >= 0, pow(x, y + z) == pow(x, y) * pow(x, z))
)
pow_one = kd.prove(kd.QForAll([x], pow(x, 1) == x), by=[pow.defn])
pow_two = kd.prove(kd.QForAll([x], pow(x, 2) == x * x), by=[pow.defn])
pow_three = kd.prove(kd.QForAll([x], pow(x, 3) == x * x * x), by=[pow.defn])
# pow_zero = kd.kernel.prove(kd.QForAll([x], x > 0, pow(x, 0) == 1), by=[pow.defn])
kd.kernel.prove(smt.Implies(x > 0, x**0 == 1))
# pow_pos = kd.prove(kd.QForAll([x, y], x > 0, pow(x, y) > 0), by=[pow.defn])

sqr = kd.define("sqr", [x], x * x)


sqrt = kd.define("sqrt", [x], x**0.5)

_l = kd.Lemma(kd.QForAll([x], x >= 0, sqrt(x) >= 0))
_ = _l.fix()
_l.unfold()
_l.auto()
sqrt_pos = _l.qed()

sqrt_define = kd.prove(smt.ForAll([x], sqrt(x) == x**0.5), by=[sqrt.defn, pow.defn])

_l = kd.Lemma(kd.QForAll([x], x >= 0, sqrt(x) ** 2 == x))
_ = _l.fix()
_l.unfold()
_l.auto()
sqrt_square = _l.qed()

sqr_sqrt = kd.prove(
    kd.QForAll([x], x >= 0, sqr(sqrt(x)) == x), by=[sqrt_square, sqr.defn]
)

_l = kd.Lemma(kd.QForAll([x], x >= 0, sqrt(sqr(x)) == x))
_ = _l.fix()
_l.unfold()
_l.auto()
sqrt_sqr = _l.qed()

exp = smt.Function("exp", R, R)  # smt.Const("exp", kd.R >> kd.R)
exp_add = kd.axiom(smt.ForAll([x, y], exp(x + y) == exp(x) * exp(y)))
exp_lower = kd.axiom(
    smt.ForAll([x], exp(x) >= 1 + x)
)  # tight low approximation at x = 0.
exp_pos = kd.axiom(smt.ForAll([x], exp(x) > 0))  # maybe we can derive this one?

exp_zero = kd.prove(smt.ForAll([x], exp(0) == 1), by=[exp_add, exp_pos])

exp_div = kd.prove(smt.ForAll([x, y], exp(x) * exp(-x) == 1), by=[exp_add, exp_zero])
exp_nzero = kd.prove(smt.ForAll([x], exp(x) != 0), by=[exp_div])
exp_inv = kd.prove(smt.ForAll([x], exp(-x) == 1 / exp(x)), by=[exp_div])


ln = smt.Function("ln", kd.R, kd.R)
ln_exp = kd.axiom(smt.ForAll([x], ln(exp(x)) == x))
# TODO. some of these are redundant depending on the range of ln being R.
ln_mul = kd.axiom(kd.QForAll([x, y], x > 0, y > 0, ln(x * y) == ln(x) + ln(y)))
ln_one = kd.prove(smt.ForAll([x], ln(1) == 0), by=[ln_exp, exp_zero])

exp_ln = kd.axiom(kd.QForAll([x], x > 0, exp(ln(x)) == x))


cos = smt.Function("cos", R, R)  # smt.Const("cos", kd.R >> kd.R)
sin = smt.Function("sin", R, R)  # smt.Const("sin", kd.R >> kd.R)

# https://en.wikipedia.org/wiki/List_of_trigonometric_identities

pythag = kd.axiom(smt.ForAll([x], cos(x) ** 2 + sin(x) ** 2 == 1))
pythag_1 = kd.prove(smt.ForAll([x], 1 - sin(x) ** 2 == cos(x) ** 2), by=[pythag])
pythag_2 = kd.prove(smt.ForAll([x], 1 - cos(x) ** 2 == sin(x) ** 2), by=[pythag])

cos_abs_le = kd.prove(smt.ForAll([x], abs(cos(x)) <= 1), by=[pythag, abs.defn])
sin_abs_le = kd.prove(smt.ForAll([x], abs(sin(x)) <= 1), by=[pythag, abs.defn])

cos_0 = kd.axiom(cos(0) == 1)
sin_0 = kd.prove(sin(0) == 0, by=[pythag, cos_0])

pi = smt.Const("pi", kd.R)
pi_bnd = kd.axiom(smt.And(3.14159 < pi, pi < 3.14160))

cos_pi = kd.axiom(cos(pi) == -1)
sin_pi = kd.prove(sin(pi) == 0, by=[pythag, cos_pi])

cos_neg = kd.axiom(smt.ForAll([x], cos(-x) == cos(x)))
sin_neg = kd.axiom(smt.ForAll([x], sin(-x) == -sin(x)))

cos_add = kd.axiom(smt.ForAll([x, y], cos(x + y) == cos(x) * cos(y) - sin(x) * sin(y)))
sin_add = kd.axiom(smt.ForAll([x, y], sin(x + y) == sin(x) * cos(y) + cos(x) * sin(y)))

_l = kd.Lemma(smt.ForAll([x, y], cos(x - y) == cos(x) * cos(y) + sin(x) * sin(y)))
_x, _y = _l.fixes()
assert isinstance(_y, smt.ArithRef)  # make typechecker stop complaining
_l.symm()
_l.eq(cos(_x + (-_y)))
_l.rw(cos_add(_x, -_y))
_l.auto(by=[cos_neg(_y), sin_neg(_y)])
_l.lemmas
cos_diff = _l.qed()

tan = kd.define("tan", [x], sin(x) / cos(x))
atan = smt.Function("atan", R, R)  # smt.Const("atan", kd.R >> kd.R)

acos = smt.Function("acos", R, R)
asin = smt.Function("asin", R, R)

comp = kd.define("comp", [f, g], smt.Lambda([x], f(g(x))))
kd.notation.matmul.register(RFun, comp)


ident = kd.define("ident", [], smt.Lambda([x], x))
const = kd.define("const", [x], smt.K(smt.RealSort(), x))
X = ident


# is_sum_convergent =
eps, delta = smt.Reals("eps delta")
# TODO. Should be less axioms
# https://en.wikipedia.org/wiki/Limit_of_a_function
delta, p, L = smt.Reals("delta p L")
has_lim_at = kd.define(
    "has_lim_at",
    [f, p, L],
    kd.QForAll(
        [eps],
        eps > smt.RealVal(0),
        kd.QExists(
            [delta],
            delta > 0,
            kd.QForAll(
                [x],
                smt.RealVal(0) < abs(x - p),
                abs(x - p) < delta,
                abs(f[x] - L) < eps,
            ),
        ),
    ),
)
lim = smt.Function("lim", RFun, R, R)
lim_def = kd.axiom(kd.QForAll([f, x, y], has_lim_at(f, x, y), lim(f, x) == y))


has_diff_at = smt.Function("has_diff_at", RFun, R, R, smt.BoolSort())
diff_at = kd.define("diff_at", [f, x], smt.Exists([y], has_diff_at(f, x, y)))
cont_at = kd.define(
    "cont_at",
    [f, x],
    kd.QForAll(
        [eps],
        eps > 0,
        kd.QExists(
            [delta],
            delta > 0,
            kd.QForAll([y], abs(x - y) < delta, abs(f[x] - f[y]) < eps),
        ),
    ),
)


# smt.Function("cont_at", RFun, R, smt.BoolSort())

is_diff = kd.define("is_diff", [f], smt.ForAll([x], diff_at(f, x)))
is_cont = kd.define("is_cont", [f], smt.ForAll([x], cont_at(f, x)))
diff_cont = kd.axiom(kd.QForAll([f], is_diff(f), is_cont(f)))

sin_diff = kd.axiom(is_diff(smt.Lambda([x], sin(x))))
sin_cont = kd.prove(is_cont(smt.Lambda([x], sin(x))), by=[sin_diff, diff_cont])


# Since not all functions are differentiable, the connection of deriv to the analytic definition of derivative is a proof obligation
deriv = smt.Function("deriv", RFun, RFun)
deriv_const = kd.axiom(ForAll([x], deriv(const(x)) == const(0)))
deriv_ident = kd.axiom(deriv(X) == const(1))
deriv_sin = kd.axiom(deriv(smt.Lambda([x], sin(x))) == smt.Lambda([x], cos(x)))
deriv_cos = kd.axiom(deriv(smt.Lambda([x], cos(x))) == smt.Lambda([x], -sin(x)))
deriv_exp = kd.axiom(deriv(smt.Lambda([x], exp(x))) == smt.Lambda([x], exp(x)))
deriv_add = kd.axiom(ForAll([f, g], deriv(f + g) == deriv(f) + deriv(g)))
deriv_mul = kd.axiom(ForAll([f, g], deriv(f * g) == deriv(f) * g + f * deriv(g)))

# Many notions of integrable.
is_integ = smt.Function("is_integ", RFun, smt.BoolSort())

integrate = smt.Function("integrate", RFun, R, R, R)
summation = smt.Function("summation", RFun, R, R, R)

Powser = kd.NewType("Powser", RSeq)
# is_convergent_at

# Bounds
# https://arxiv.org/pdf/0708.3721
# Marc Daumas, David Lester, and César Munoz. 2008. Verified real number calculations:
# A library for interval arithmetic. IEEE Trans. Comput. 58, 2 (2008), 226–237.


def sqrt_upper(x, n):
    assert n >= 0
    if n == 0:
        return x + 1
    else:
        y = sqrt_upper(x, n - 1)
        return (y + x / y) / 2


def sqrt_lower(n, x):
    assert n >= 0
    return x / sqrt_upper(x, n)


def sqrt_bnd(n):
    x = smt.Real("x")
    return kd.axiom(
        kd.QForAll(
            [x],
            x >= 0,
            smt.And(sqrt_lower(x, n) <= sqrt(x), sqrt(x) <= sqrt_upper(x, n)),
        )
    )


def sin_lower(n, x):
    assert n >= 0
    sum(x**n)
