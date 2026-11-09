"""
Definitions about the reals.

Transcendental functions and bounds.
"""

import kdrag.smt as smt
from kdrag.smt import (
    Abs,
    And,
    ArraySort,
    BoolSort,
    Const,
    Consts,
    Exists,
    ForAll,
    Function,
    If,
    Implies,
    Int,
    IntSort,
    Ints,
    K,
    Lambda,
    Real,
    RealSort,
    RealVal,
    Reals,
    ToInt,
    ToReal,
    is_app,
    is_var,
)
import kdrag.theories.set as set_
import kdrag as kd
from kdrag import Lemma, NewType, QExists, QForAll, Theorem, axiom, cond, define, prove

T = RealSort()

R = RealSort()
RFun = ArraySort(R, R)
RSeq = ArraySort(IntSort(), R)
RSet = set_.Set(R)
S = RSet.full

real_db = []
real_simp = []


def rlemma(thm, by=[], **kwargs):
    return prove(thm, by + real_db + real_simp, **kwargs)


x, y, z, eps = Reals("x y z eps")

f, g = Consts("f g", RFun)

fadd = kd.notation.add.define([f, g], Lambda([x], f[x] + g[x]))
fsub = kd.notation.sub.define([f, g], Lambda([x], f[x] - g[x]))
fmul = kd.notation.mul.define([f, g], Lambda([x], f[x] * g[x]))
fdiv = kd.notation.div.define([f, g], Lambda([x], f[x] / g[x]))

poly = Function("poly", RFun, BoolSort())
axiom(ForAll([x], poly(K(RealSort(), x))))
axiom(poly(Lambda([x], x)))
axiom(QForAll([f, g], poly(f), poly(g), poly(f + g)))
axiom(QForAll([f, g], poly(f), poly(g), poly(f * g)))


# NReal = kd.NewType("NReal", R)

zero = define("R.zero", [], RealVal(0))


add = define("R.add", [x, y], x + y)

add_0 = prove(ForAll([x], add(x, 0) == x), by=[add.defn])
add_comm = prove(ForAll([x, y], add(x, y) == add(y, x)), by=[add.defn])
add_assoc = prove(
    ForAll([x, y, z], add(x, add(y, z)) == add(add(x, y), z)), by=[add.defn]
)


class Add:
    f = add
    comm = add_comm
    assoc = add_assoc
    e = RealVal(0)
    left_id = prove(ForAll([x], add(0, x) == x), by=[add.defn])
    right_id = prove(ForAll([x], add(x, 0) == x), by=[add.defn])


sub = define("sub", [x, y], x - y)
sub_0 = prove(ForAll([x], sub(x, 0) == x), by=[sub.defn])
sub_add = prove(
    ForAll([x, y, z], (add(x, y) == z) == (x == sub(z, y))), by=[sub.defn, add.defn]
)

mul = define("mul", [x, y], x * y)
mul_zero = prove(ForAll([x], mul(x, 0) == 0), by=[mul.defn])
one = define("one", [], RealVal(1))
mul_one = prove(ForAll([x], mul(x, one) == x), by=[mul.defn, one.defn])
one_mul = prove(ForAll([x], mul(one, x) == x), by=[mul.defn, one.defn])
mul_comm = prove(ForAll([x, y], mul(x, y) == mul(y, x)), by=[mul.defn])
# mul_assoc = kd.prove(
#    ForAll([x, y, z], mul(x, mul(y, z)) == mul(mul(x, y), z)), by=[mul.defn]
# )
_l = Lemma(ForAll([x, y, z], mul(x, mul(y, z)) == mul(mul(x, y), z)))
_x, _y, _z = _l.fixes()
_l.unfold()
_l.auto()
mul_assoc = _l.qed()


class Mul:
    f = mul
    comm = mul_comm
    assoc = mul_assoc
    e = RealVal(1)
    left_id = prove(ForAll([x], mul(1, x) == x), by=[mul.defn])
    right_id = prove(ForAll([x], mul(x, 1) == x), by=[mul.defn])


mul_distrib = prove(
    ForAll([x, y, z], mul(x, add(y, z)) == add(mul(x, y), mul(x, z))),
    by=[mul.defn, add.defn],
)


def abstract_arith(t: smt.ExprRef) -> smt.ExprRef:
    """
    Z3 has difficult ematching over arithmetic expressions.
    Abstracting them to uninterpreted functions can help.
    """
    if is_var(t):
        return t
    elif is_app(t):
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


abs = define("absR", [x], If(x >= 0, x, -x))
sgn = define("sgn", [x], If(x > 0, 1, If(x < 0, -1, 0)))

abs_if_pos = prove(ForAll([x], x >= 0, abs(x) == x), by=[abs.defn])
sgn_abs = prove(ForAll([x], abs(x) * sgn(x) == x), by=[abs.defn, sgn.defn])
abs_le = prove(ForAll([x, y], (abs(x) <= y) == And(-y <= x, x <= y)), by=[abs.defn])
abs_idem = prove(ForAll([x], abs(abs(x)) == abs(x)), by=[abs.defn])
abs_neg = prove(ForAll([x], abs(-x) == abs(x)), by=[abs.defn])
abs_pos = prove(ForAll([x], abs(x) >= 0), by=[abs.defn])
# TODO: kd.contract(abs, [x], smt.BoolVal(True), abs(x) >= 0, by=[abs_pos])
abs_add = prove(ForAll([x, y], abs(x + y) <= abs(x) + abs(y)), by=[abs.defn])
abs_mul = prove(ForAll([x, y], abs(x * y) == abs(x) * abs(y)), by=[abs.defn])
abs_div = prove(
    ForAll([x, y], Implies(y != 0, abs(x / y) == abs(x) / abs(y))),
    by=[abs.defn],
)
abs_Lipschitz = prove(ForAll([x, y], abs(abs(x) - abs(y)) <= abs(x - y)), by=[abs.defn])
abs_triangle = prove(
    ForAll([x, y, z], abs(x - y) <= abs(x - z) + abs(z - y)), by=[abs.defn]
)
abs_eq_zero = prove(
    QForAll([x], (abs(x) == 0) == (x == 0)),
    by=[abs.defn],
)

abs_pos_iff = prove(
    QForAll([x], (abs(x) > 0) == (x != 0)),
    by=[abs_eq_zero, abs_pos],
)
# TODO: abs_convex

aeq = define("aeq", [x, y, eps], Abs(x - y) <= eps)
aeq_pos = prove(QForAll([x, y, eps], aeq(x, y, eps), eps >= 0), by=[aeq.defn])
aeq_refl = prove(QForAll([x], aeq(x, x, 0)), by=[aeq.defn])
aeq_symm = prove(QForAll([x, y, eps], aeq(x, y, eps) == aeq(y, x, eps)), by=[aeq.defn])
eps1, eps2 = Reals("eps1 eps2")
aeq_trans = prove(
    QForAll([x, y, z, eps], aeq(x, y, eps1), aeq(y, z, eps2), aeq(x, z, eps1 + eps2)),
    by=[aeq.defn],
)
aeq_weak = prove(
    QForAll([x, y, eps1, eps2], eps1 <= eps2, aeq(x, y, eps1), aeq(x, y, eps2)),
    by=[aeq.defn],
)


nonneg = define("nonneg", [x], abs(x) == x)
nonneg_ge_0 = prove(ForAll([x], nonneg(x) == (x >= 0)), by=[nonneg.defn, abs.defn])

max = define("R.max", [x, y], If(x >= y, x, y))
max_le = prove(ForAll([x, y], (x <= y) == (max(x, y) == y)), by=[max.defn])
max_comm = prove(ForAll([x, y], max(x, y) == max(y, x)), by=[max.defn])
max_assoc = prove(
    ForAll([x, y, z], max(x, max(y, z)) == max(max(x, y), z)), by=[max.defn]
)
max_idem = prove(ForAll([x], max(x, x) == x), by=[max.defn])
max_ge = prove(ForAll([x, y], max(x, y) >= x), by=[max.defn])
max_ge_2 = prove(ForAll([x, y], max(x, y) >= y), by=[max.defn])

min = define("min", [x, y], If(x <= y, x, y))
min_le = prove(ForAll([x, y], (x <= y) == (min(x, y) == x)), by=[min.defn])
min_comm = prove(ForAll([x, y], min(x, y) == min(y, x)), by=[min.defn])
min_assoc = prove(
    ForAll([x, y, z], min(x, min(y, z)) == min(min(x, y), z)), by=[min.defn]
)
min_idem = prove(ForAll([x], min(x, x) == x), by=[min.defn])
min_le_2 = prove(ForAll([x, y], min(x, y) <= x), by=[min.defn])
min_le_3 = prove(ForAll([x, y], min(x, y) <= y), by=[min.defn])


n, m = Ints("n m")
to_real_add = prove(ForAll([n, m], ToReal(n + m) == ToReal(n) + ToReal(m)))
to_real_sub = prove(ForAll([n, m], ToReal(n - m) == ToReal(n) - ToReal(m)))
to_real_mul = prove(ForAll([n, m], ToReal(n * m) == ToReal(n) * ToReal(m)))
to_real_neg = prove(ForAll([n], ToReal(-n) == -ToReal(n)))
to_real_inj = prove(ForAll([n, m], (ToReal(n) == ToReal(m)) == (n == m)))
to_real_mono = prove(ForAll([n, m], (n < m) == (ToReal(n) < ToReal(m))))

floor = define("floor", [x], ToReal(ToInt(x)))
n = Int("n")
int_real_galois_lt = prove(ForAll([x, n], (x < ToReal(n)) == (ToInt(x) < n)))
int_real_galois_le = prove(ForAll([x, n], (ToReal(n) <= x) == (n <= ToInt(x))))

_2 = prove(ForAll([x], ToInt(floor(x)) == ToInt(x)), by=[floor.defn])
floor_idem = prove(ForAll([x], floor(floor(x)) == floor(x)), by=[floor.defn, _2])
floor_le = prove(ForAll([x], floor(x) <= x), by=[floor.defn])
floor_gt = prove(ForAll([x], x < floor(x) + 1), by=[floor.defn])


ceil = define("ceil", [x], -floor(-x))
ceil_le = prove(ForAll([x], x <= ceil(x)), by=[ceil.defn, floor_le])
ceil_gt = prove(ForAll([x], ceil(x) - 1 < x), by=[ceil.defn, floor_gt])
# c = kd.Calc([n, x], smt.ToReal(n) <= x)
# c.eq(n <= smt.ToInt(x))
# c.eq(smt.ToReal(n) <= floor(x), by=[floor.defn])
# floor_minint = c.qed(defns=False)


pow = define("pow", [x, y], x**y)
pow_add = axiom(QForAll([x, y, z], x >= 0, pow(x, y + z) == pow(x, y) * pow(x, z)))
pow_one = prove(QForAll([x], pow(x, 1) == x), by=[pow.defn])
pow_two = prove(QForAll([x], pow(x, 2) == x * x), by=[pow.defn])
pow_three = prove(QForAll([x], pow(x, 3) == x * x * x), by=[pow.defn])
# pow_zero = kd.kernel.prove(kd.QForAll([x], x > 0, pow(x, 0) == 1), by=[pow.defn])
kd.kernel.prove(Implies(x > 0, x**0 == 1))
# pow_pos = kd.prove(kd.QForAll([x, y], x > 0, pow(x, y) > 0), by=[pow.defn])

pownat = Function("pownat", RealSort(), IntSort(), RealSort())
pownat = define(
    "pownat",
    [x, n],
    cond((n == 0, 1), (n > 0, x * pownat(x, n - 1)), default=pownat(x, n + 1) / x),
)

# Basic lemmas for pownat.
pownat_zero = prove(
    ForAll([x], pownat(x, 0) == 1),
    by=[pownat.defn],
)
pownat_succ = prove(
    QForAll([x, n], n >= 0, pownat(x, n + 1) == x * pownat(x, n)),
    by=[pownat.defn],
)

sqr = define("R.sqr", [x], x * x)
sqr_pos = prove(
    ForAll([x], sqr(x) >= 0),
    by=[sqr.defn],
)
# kd.contract(sqr, [x], smt.BoolVal(True), sqr(x) >= 0, by=[sqr_pos]) # tests are loading and reloading this file/ That's not great anyway?
sqr_neg = prove(ForAll([x], sqr(-x) == sqr(x)), by=[sqr.defn])

# Note that guarding under Real prefix prevents clash with cvc5 built-ins. For better and worse
sqrt = define("Real.sqrt", [x], x ** "1/2")
# sqrt = kd.define("sqrt", [x], smt.If(x >= 0, x ** "1/2", kd.Undef(smt.RealSort(), x)))
# sqrt
_l = Lemma(QForAll([x], x >= 0, sqrt(x) >= 0))
_ = _l.fix()
_l.unfold()
_l.auto()
sqrt_pos = _l.qed()

# kd.contract(sqrt, [x], x >= 0, sqrt(x) >= 0, by=[sqrt_pos])

sqrt_define = prove(ForAll([x], sqrt(x) == x**0.5), by=[sqrt.defn, pow.defn])

sqrt_one = prove(sqrt(1) == 1, by=[sqrt.defn])
sqrt_zero = prove(sqrt(0) == 0, by=[sqrt.defn])
_l = Lemma(QForAll([x], x >= 0, sqrt(x) ** 2 == x))
_ = _l.fix()
_l.unfold()
_l.auto()
sqrt_square = _l.qed()

sqr_sqrt = prove(QForAll([x], x >= 0, sqr(sqrt(x)) == x), by=[sqrt_square, sqr.defn])


sqrt_mul = prove(
    QForAll([x, y], x >= 0, y >= 0, sqrt(x * y) == sqrt(x) * sqrt(y)),
    by=[sqrt.defn, mul.defn],
)
sqrt_mono = prove(
    QForAll([x, y], x >= 0, y >= 0, x <= y, sqrt(x) <= sqrt(y)),
    by=[sqrt.defn],
)

_l = Lemma(QForAll([x], x >= 0, sqrt(sqr(x)) == x))
_ = _l.fix()
_l.unfold()
_l.auto()
sqrt_sqr = _l.qed()

sqrt_sqr_neg = prove(QForAll([x], x <= 0, sqrt(sqr(x)) == -x), by=[sqrt_sqr, sqr_neg])

sqrt_sqr_abs = prove(
    QForAll([x], sqrt(sqr(x)) == abs(x)),
    by=[abs.defn, sqrt_sqr, sqrt_sqr_neg, sqr_pos],
)

exp = Function("Real.exp", R, R)  # smt.Const("exp", kd.R >> kd.R)
exp_add = axiom(ForAll([x, y], exp(x + y) == exp(x) * exp(y)))
exp_lower = axiom(ForAll([x], exp(x) >= 1 + x))  # tight low approximation at x = 0.
exp_pos = axiom(ForAll([x], exp(x) > 0))  # maybe we can derive this one?
exp_range = exp_pos
# kd.contract(exp, [x], smt.BoolVal(True), exp(x) > 0, by=[exp_pos])
exp_pos_ge_one = prove(ForAll([x], x >= 0, exp(x) >= 1), by=[exp_lower])

exp_zero = prove(ForAll([x], exp(0) == 1), by=[exp_add, exp_pos])

exp_div = prove(ForAll([x, y], exp(x) * exp(-x) == 1), by=[exp_add, exp_zero])
exp_nzero = prove(ForAll([x], exp(x) != 0), by=[exp_div])
exp_inv = prove(ForAll([x], exp(-x) == 1 / exp(x)), by=[exp_div])


@Theorem(ForAll([x, y], x <= y, exp(x) <= exp(y)))
def exp_mono(l):
    # exp(x) <= exp(x) * exp(y-x) == exp(y)
    x, y = l.fixes()
    _x_ge_y = l.intro()
    l.have(exp(y) == exp(y - x) * exp(x), by=[exp_add(y - x, x)])
    l.have(exp(y - x) >= 1, by=[exp_pos_ge_one(y - x)])
    l.auto(by=[exp_pos])


exp_neg_le_1 = prove(ForAll([x], x <= 0, exp(x) <= 1), by=[exp_mono, exp_zero])

ln = Function("Real.ln", kd.R, kd.R)
ln_exp = axiom(ForAll([x], ln(exp(x)) == x))
# TODO. some of these are redundant depending on the range of ln being R.
ln_mul = axiom(QForAll([x, y], x > 0, y > 0, ln(x * y) == ln(x) + ln(y)))
ln_one = prove(ForAll([x], ln(1) == 0), by=[ln_exp, exp_zero])

exp_ln = axiom(QForAll([x], x > 0, exp(ln(x)) == x))


cos = Function("Real.cos", R, R)  # smt.Const("cos", kd.R >> kd.R)
sin = Function("Real.sin", R, R)  # smt.Const("sin", kd.R >> kd.R)

# https://en.wikipedia.org/wiki/List_of_trigonometric_identities

pythag = axiom(ForAll([x], cos(x) ** 2 + sin(x) ** 2 == 1))
pythag_1 = prove(ForAll([x], 1 - sin(x) ** 2 == cos(x) ** 2), by=[pythag])
pythag_2 = prove(ForAll([x], 1 - cos(x) ** 2 == sin(x) ** 2), by=[pythag])

cos_range = prove(ForAll([x], And(cos(x) >= -1, cos(x) <= 1)), by=[pythag])
sin_range = prove(ForAll([x], And(sin(x) >= -1, sin(x) <= 1)), by=[pythag])
cos_abs_le = prove(ForAll([x], abs(cos(x)) <= 1), by=[cos_range, abs.defn])
sin_abs_le = prove(ForAll([x], abs(sin(x)) <= 1), by=[sin_range, abs.defn])

cos_0 = axiom(cos(0) == 1)
sin_0 = prove(sin(0) == 0, by=[pythag, cos_0])

pi = Const("pi", kd.R)
pi_bnd = axiom(And(3.14159 < pi, pi < 3.14160))

cos_pi = axiom(cos(pi) == -1)
sin_pi = prove(sin(pi) == 0, by=[pythag, cos_pi])

cos_neg = axiom(ForAll([x], cos(-x) == cos(x)))
sin_neg = axiom(ForAll([x], sin(-x) == -sin(x)))

cos_add = axiom(ForAll([x, y], cos(x + y) == cos(x) * cos(y) - sin(x) * sin(y)))
sin_add = axiom(ForAll([x, y], sin(x + y) == sin(x) * cos(y) + cos(x) * sin(y)))

_l = Lemma(ForAll([x, y], cos(x - y) == cos(x) * cos(y) + sin(x) * sin(y)))
_x, _y = _l.fixes()
assert isinstance(_y, smt.ArithRef)  # make typechecker stop complaining
_l.symm()
_l.eq(cos(_x + (-_y)))
_l.rw(cos_add(_x, -_y))
_l.auto(by=[cos_neg(_y), sin_neg(_y)])
_l.lemmas
cos_diff = _l.qed()

tan = define("tan", [x], sin(x) / cos(x))
atan = Function("atan", R, R)  # smt.Const("atan", kd.R >> kd.R)

acos = Function("acos", R, R)
acos_cos = axiom(QForAll([x], x >= -1, x <= 1, cos(acos(x)) == x))
acos_range = axiom(QForAll([x], x >= -1, x <= 1, And(acos(x) >= 0, acos(x) <= pi)))
asin = Function("asin", R, R)
asin_sin = axiom(QForAll([x], x >= -1, x <= 1, sin(asin(x)) == x))
asin_range = axiom(
    QForAll([x], x >= -1, x <= 1, And(asin(x) >= -pi / 2, asin(x) <= pi / 2))
)

comp = define("comp", [f, g], Lambda([x], f(g(x))))
kd.notation.matmul.register(RFun, comp)


ident = define("RFun.ident", [], Lambda([x], x))
const = define("RFun.const", [x], K(RealSort(), x))
X = ident


# is_sum_convergent =
eps, delta = Reals("eps delta")
# TODO. Should be less axioms
# https://en.wikipedia.org/wiki/Limit_of_a_function
delta, p, L = Reals("delta p L")
has_lim_at = define(
    "has_lim_at",
    [f, p, L],
    QForAll(
        [eps],
        eps > RealVal(0),
        QExists(
            [delta],
            delta > 0,
            QForAll(
                [x],
                RealVal(0) < abs(x - p),
                abs(x - p) < delta,
                abs(f[x] - L) < eps,
            ),
        ),
    ),
)
lim = Function("lim", RFun, R, R)
lim_def = axiom(QForAll([f, x, y], has_lim_at(f, x, y), lim(f, x) == y))


has_diff_at = Function("has_diff_at", RFun, R, R, BoolSort())
diff_at = define("diff_at", [f, x], Exists([y], has_diff_at(f, x, y)))
cont_at = define(
    "cont_at",
    [f, x],
    QForAll(
        [eps],
        eps > 0,
        QExists(
            [delta],
            delta > 0,
            QForAll([y], abs(x - y) < delta, abs(f[x] - f[y]) < eps),
        ),
    ),
)


# x, y = smt.Reals("x y")
N = Int("N")


@Theorem(
    ForAll(
        [x, y],
        Implies(
            And(x > 0, y > 0),
            Exists([N], y < x * N),
        ),
    )
)
def archimedes(l):
    # https://en.wikipedia.org/wiki/Archimedean_property
    x, y = l.fixes()
    l.intro()

    # Choose N = floor(y/x) + 1.
    l.exists(ToInt(y / x) + 1)
    l.auto()


# smt.Function("cont_at", RFun, R, smt.BoolSort())

is_diff = define("is_diff", [f], ForAll([x], diff_at(f, x)))
is_cont = define("is_cont", [f], ForAll([x], cont_at(f, x)))
diff_cont = axiom(QForAll([f], is_diff(f), is_cont(f)))

sin_diff = axiom(is_diff(Lambda([x], sin(x))))
sin_cont = prove(is_cont(Lambda([x], sin(x))), by=[sin_diff, diff_cont])


# Since not all functions are differentiable, the connection of deriv to the analytic definition of derivative is a proof obligation
deriv = Function("deriv", RFun, RFun)
deriv_const = axiom(ForAll([x], deriv(const(x)) == const(0)))
deriv_ident = axiom(deriv(X) == const(1))
deriv_sin = axiom(deriv(Lambda([x], sin(x))) == Lambda([x], cos(x)))
deriv_cos = axiom(deriv(Lambda([x], cos(x))) == Lambda([x], -sin(x)))
deriv_exp = axiom(deriv(Lambda([x], exp(x))) == Lambda([x], exp(x)))
deriv_add = axiom(ForAll([f, g], deriv(f + g) == deriv(f) + deriv(g)))
deriv_mul = axiom(ForAll([f, g], deriv(f * g) == deriv(f) * g + f * deriv(g)))

# Many notions of integrable.
is_integ = Function("is_integ", RFun, BoolSort())

integrate = Function("integrate", RFun, R, R, R)
summation = Function("summation", RFun, R, R, R)

Powser = NewType("Powser", RSeq)
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
    x = Real("x")
    return axiom(
        QForAll(
            [x],
            x >= 0,
            And(sqrt_lower(x, n) <= sqrt(x), sqrt(x) <= sqrt_upper(x, n)),
        )
    )


def sin_lower(n, x):
    assert n >= 0
    sum(x**n)
