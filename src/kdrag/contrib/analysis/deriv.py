"""Pointwise differentiation defined by the difference-quotient limit.

Linearity follows from the limit rules in `cont`, using that a limit at p ignores
the value at p (the quotient is 0/0 there). The chain rule goes through
Carathéodory's characterisation, which avoids dividing by f(x) - f(p).
"""

from kdrag import Theorem, define, prove
import kdrag.smt as smt
from kdrag.smt import (
    And,
    Const,
    Consts,
    Eq,
    Exists,
    ForAll,
    Lambda,
    Or,
    Reals,
    RealVal,
    Store,
)

from kdrag.theories.real import RFun, abs, abs_mul, cont_at, fmul, has_lim_at, min
from kdrag.contrib.analysis.cont import (
    cont_at_comp,
    has_lim_at_congr,
    has_lim_at_const,
    has_lim_at_id,
)
from kdrag.theories.real.cont import (
    cont_at_update_of_has_lim_at,
    has_lim_at_of_cont_at,
    has_lim_at_add,
    has_lim_at_mul,
)

f, g = Consts("f g", RFun)
x, p, L, a, b, c = Reals("x p L a b c")
F = Const("F", RFun)
k, t, u, v, y, eps, delta = Reals("k t u v y eps delta")
lo, hi = Reals("lo hi")


# The single derivative predicate: derivative value first, then the base point.
has_deriv_at = define(
    "has_deriv_at",
    [f, a, p],
    has_lim_at(Lambda(x, (f[x] - f[p]) / (x - p)), p, a),
)


def quot(f, p):
    """The difference quotient of f at p."""
    return Lambda(x, (f[x] - f[p]) / (x - p))


@Theorem(
    ForAll(
        [f, a, p],
        Eq(
            has_deriv_at(f, a, p),
            ForAll(
                eps,
                eps > 0,
                Exists(
                    delta,
                    delta > 0,
                    ForAll(
                        y,
                        abs(y - p) < delta,
                        abs(f[y] - f[p] - a * (y - p)) <= eps * abs(y - p),
                    ),
                ),
            ),
        ),
    )
)
def has_deriv_at_iff_remainder(l):
    """The linear-remainder estimate follows from, and characterizes, the limit."""
    f, a, p = l.fixes()
    l.unfold(has_deriv_at)
    l.split()
    # A strict quotient bound gives the non-strict remainder bound off p.
    h = l.intro()
    l.unfold(has_lim_at, at=h)
    h = l.top_goal().ctx[-1]
    e = l.fix()
    l.intro()
    positive = l.have(RealVal(0) < e, by=[])
    d, _ = l.obtain(l.specialize(h, e, positive))
    l.split(at=0)
    near = l.top_goal().ctx[1]
    l.exists(d)
    l.split()
    l.auto()
    z = l.fix()
    l.intro()
    l.cases(z == p)
    l.auto(by=[abs.defn(0)])
    l.have(abs(quot(f, p)[z] - a) < e, by=[abs.defn(z - p)])
    l.clear(near)
    l.have((quot(f, p)[z] - a) * (z - p) == f[z] - f[p] - a * (z - p), by=[])
    l.auto(by=[abs_mul(quot(f, p)[z] - a, z - p), abs.defn(z - p)])
    # Conversely, use half epsilon to turn <= into < after division.
    h = l.intro()
    l.unfold(has_lim_at)
    e = l.fix()
    l.intro()
    positive = l.have(e / 2 > 0, by=[])
    d, _ = l.obtain(l.specialize(h, e / 2, positive))
    l.split(at=0)
    near = l.top_goal().ctx[1]
    l.exists(d)
    l.split()
    l.auto()
    z = l.fix()
    l.intros()
    l.have(abs(f[z] - f[p] - a * (z - p)) <= e / 2 * abs(z - p), by=[])
    l.clear(near)
    l.have(
        (quot(f, p)[z] - a) * (z - p) == f[z] - f[p] - a * (z - p), by=[abs.defn(z - p)]
    )
    l.have(
        abs(quot(f, p)[z] - a) * abs(z - p) == abs(f[z] - f[p] - a * (z - p)),
        by=[abs_mul(quot(f, p)[z] - a, z - p)],
    )
    l.auto(by=[abs.defn(z - p)])


@Theorem(ForAll([c, p], has_deriv_at(Lambda(x, c), 0, p)))
def has_deriv_at_const(l):
    c, p = l.fixes()
    l.unfold(has_deriv_at)
    # The quotient (c - c) / (x - p) is 0 away from p.
    zero = Lambda(x, RealVal(0))
    l.auto(
        by=[has_lim_at_congr(zero, quot(Lambda(x, c), p), p, 0), has_lim_at_const(0, p)]
    )


@Theorem(ForAll([p], has_deriv_at(Lambda(x, x), 1, p)))
def has_deriv_at_id(l):
    p = l.fix()
    l.unfold(has_deriv_at)
    # The quotient (x - p) / (x - p) is 1 away from p.
    one = Lambda(x, RealVal(1))
    l.auto(
        by=[has_lim_at_congr(one, quot(Lambda(x, x), p), p, 1), has_lim_at_const(1, p)]
    )


@Theorem(
    ForAll(
        [f, g, p, a, b],
        has_deriv_at(f, a, p),
        has_deriv_at(g, b, p),
        has_deriv_at(f + g, a + b, p),
    )
)
def has_deriv_at_add(l):
    f, g, p, a, b = l.fixes()
    l.intros()
    l.unfold(has_deriv_at)
    qf, qg = quot(f, p), quot(g, p)
    l.have(has_lim_at(qf, p, a), by=[has_deriv_at.defn(f, a, p)])
    l.have(has_lim_at(qg, p, b), by=[has_deriv_at.defn(g, b, p)])
    l.have(has_lim_at(qf + qg, p, a + b), by=[has_lim_at_add(qf, qg, p, a, b)])
    # The quotient of f + g is the sum of the quotients away from p.
    l.auto(by=[has_lim_at_congr(qf + qg, quot(f + g, p), p, a + b)])


@Theorem(
    ForAll(
        [c, f, p, a],
        has_deriv_at(f, a, p),
        has_deriv_at(Lambda(x, c * f[x]), c * a, p),
    )
)
def has_deriv_at_const_mul(l):
    c, f, p, a = l.fixes()
    l.intro()
    l.unfold(has_deriv_at)
    qf, cf = quot(f, p), Lambda(x, c)
    l.have(has_lim_at(qf, p, a), by=[has_deriv_at.defn(f, a, p)])
    l.have(
        has_lim_at(cf * qf, p, c * a),
        by=[has_lim_at_mul(cf, qf, p, c, a), has_lim_at_const(c, p)],
    )
    # c times the quotient of f is the quotient of c * f away from p.
    target = quot(Lambda(x, c * f[x]), p)
    congr = ForAll(x, x != p, (cf * qf)[x] == target[x])
    # Isolate the rational identity from the quantified limit hypotheses.
    l.have(congr, by=[prove(congr, by=[fmul.defn])])
    l.auto(by=[has_lim_at_congr(cf * qf, target, p, c * a)])


# Carathéodory: f is differentiable at p with derivative a iff
# f(x) - f(p) = slope(x) * (x - p) for a slope continuous at p with slope(p) = a.


def slope(f, p, a):
    """The difference quotient of f at p, patched to a at p."""
    return Store(quot(f, p), p, a)


@Theorem(ForAll([f, p, a, x], f[x] - f[p] == slope(f, p, a)[x] * (x - p)))
def sub_eq_slope_mul(l):
    l.fixes()
    l.auto()


@Theorem(ForAll([f, p, a], has_deriv_at(f, a, p), cont_at(slope(f, p, a), p)))
def cont_at_slope_of_has_deriv_at(l):
    f, p, a = l.fixes()
    l.intro()
    l.auto(
        by=[has_deriv_at.defn(f, a, p), cont_at_update_of_has_lim_at(quot(f, p), p, a)]
    )


@Theorem(ForAll([f, p, a], has_deriv_at(f, a, p), cont_at(f, p)))
def cont_at_of_has_deriv_at(l):
    """A differentiable function is continuous."""
    f, p, a = l.fixes()
    l.intro()
    s, lin, fp = slope(f, p, a), Lambda(x, x - p), Lambda(x, f[p])
    # The slope tends to a and x - p tends to 0 ...
    l.have(
        has_lim_at(s, p, a),
        by=[has_lim_at_of_cont_at(s, p), cont_at_slope_of_has_deriv_at(f, p, a)],
    )
    l.have(
        has_lim_at(lin, p, 0),
        by=[
            has_lim_at_add(Lambda(x, x), Lambda(x, -p), p, p, -p),
            has_lim_at_id(p),
            has_lim_at_const(-p, p),
            has_lim_at_congr(Lambda(x, x + -p), lin, p, 0),
        ],
    )
    # ... so f = f(p) + slope * (x - p) tends to f(p).
    l.have(has_lim_at(s * lin, p, 0), by=[has_lim_at_mul(s, lin, p, a, 0)])
    l.have(
        has_lim_at(fp + s * lin, p, f[p]),
        by=[has_lim_at_add(fp, s * lin, p, f[p], 0), has_lim_at_const(f[p], p)],
    )
    # Check the extensional identity without the quantified limit hypotheses.
    identity = prove(fp + s * lin == f, by=[fmul.defn])
    l.have(fp + s * lin == f, by=[identity])
    l.have(has_lim_at(f, p, f[p]), by=[])
    l.have(Store(f, p, f[p]) == f, by=[])
    l.auto(by=[cont_at_update_of_has_lim_at(f, p, f[p])])


@Theorem(
    ForAll(
        [f, g, p, a, b, x],
        x != p,
        quot(Lambda(x, g[f[x]]), p)[x] == slope(g, f[p], b)[f[x]] * slope(f, p, a)[x],
    )
)
def quot_comp_eq(l):
    """Away from p, the quotient of g ∘ f factors through the two slopes."""
    f, g, p, a, b, x = l.fixes()
    l.intro()
    l.auto(by=[sub_eq_slope_mul(f, p, a, x), sub_eq_slope_mul(g, f[p], b, f[x])])


@Theorem(
    ForAll(
        [f, g, p, a, b],
        has_deriv_at(f, a, p),
        has_deriv_at(g, b, f[p]),
        has_deriv_at(Lambda(x, g[f[x]]), b * a, p),
    )
)
def has_deriv_at_comp(l):
    """The chain rule."""
    f, g, p, a, b = l.fixes()
    l.intros()
    sf, sg = slope(f, p, a), slope(g, f[p], b)
    sgf = Lambda(x, sg[f[x]])
    # sg(f x) tends to sg(f p) = b, since f is continuous and sg continuous at f(p).
    l.have(cont_at(f, p), by=[cont_at_of_has_deriv_at(f, p, a)])
    l.have(cont_at(sg, f[p]), by=[cont_at_slope_of_has_deriv_at(g, f[p], b)])
    l.have(cont_at(sgf, p), by=[cont_at_comp(f, sg, p)])
    l.have(has_lim_at(sgf, p, b), by=[has_lim_at_of_cont_at(sgf, p)])
    # sf tends to a.
    l.have(
        has_lim_at(sf, p, a),
        by=[has_lim_at_of_cont_at(sf, p), cont_at_slope_of_has_deriv_at(f, p, a)],
    )
    l.have(has_lim_at(sgf * sf, p, b * a), by=[has_lim_at_mul(sgf, sf, p, b, a)])
    # Prove the pointwise identity before transporting the product limit.
    target = quot(Lambda(x, g[f[x]]), p)
    l.have(ForAll(x, x != p, (sgf * sf)[x] == target[x]))
    z = l.fix()
    l.intro()
    l.auto(by=[fmul.defn(sgf, sf), quot_comp_eq(f, g, p, a, b, z)])
    l.unfold(has_deriv_at)
    l.auto(by=[has_lim_at_congr(sgf * sf, target, p, b * a)])


def straddles(F, k, t, delta, eps) -> smt.BoolRef:
    """Every interval around `t` inside the `delta` ball is within `eps` of slope `k`."""
    return ForAll(
        [u, v],
        t - delta < u,
        u <= t,
        t <= v,
        v < t + delta,
        abs(F[v] - F[u] - k * (v - u)) <= eps * (v - u),
    )


@Theorem(
    ForAll(
        [F, k, t, eps],
        has_deriv_at(F, k, t),
        eps > 0,
        Exists(delta, delta > 0, straddles(F, k, t, delta, eps)),
    )
)
def straddle_of_has_deriv_at(l):
    F, k, t, eps = l.fixes()
    l.rw(has_deriv_at_iff_remainder)
    h = l.intro()
    l.intro()
    positive = l.have(eps / 2 > 0, by=[])
    r, _ = l.obtain(l.specialize(h, eps / 2, positive))
    l.split(at=0)
    near = l.top_goal().ctx[1]
    l.exists(r)
    l.split()
    l.assumption()
    u, v = l.fixes()
    l.intros()
    # Split [u, v] at t and compare each half with the tangent line at t.
    l.have(abs(F[u] - F[t] - k * (u - t)) <= eps / 2 * abs(u - t), by=[abs.defn(u - t)])
    l.have(abs(F[v] - F[t] - k * (v - t)) <= eps / 2 * abs(v - t), by=[abs.defn(v - t)])
    l.clear(near)
    l.auto(
        by=[
            abs.defn(u - t),
            abs.defn(v - t),
            abs.defn(F[v] - F[u] - k * (v - u)),
            abs.defn(F[u] - F[t] - k * (u - t)),
            abs.defn(F[v] - F[t] - k * (v - t)),
        ]
    )


@Theorem(
    ForAll(
        [f, a, p, lo, hi],
        lo < p,
        p < hi,
        has_deriv_at(f, a, p),
        Or(
            ForAll(x, lo < x, x < hi, f[x] <= f[p]),
            ForAll(x, lo < x, x < hi, f[p] <= f[x]),
        ),
        a == 0,
    )
)
def deriv_eq_zero_of_interior_extremum(l):
    """Abbott 5.2.6, the interior extremum theorem."""
    f, a, p, lo, hi = l.fixes()
    l.rw(has_deriv_at_iff_remainder(f, a, p))
    _, _, differentiable, extremum = l.intros()
    l.contra()
    error = abs(a) / 2
    positive = l.have(error > 0, by=[abs.defn(a)])
    radius, witness = l.obtain(l.specialize(differentiable, error, positive))
    _, estimate = l.andE(witness)

    # Test the remainder estimate at one point on each side of p.
    left_step, right_step = min(radius, p - lo) / 2, min(radius, hi - p) / 2
    left, right = p - left_step, p + right_step
    nearby = l.have(
        Exists(
            [u, v],
            And(lo < u, u < p, p < v, v < hi, abs(u - p) < radius, abs(v - p) < radius),
        )
    )
    l.exists(left, right)
    l.auto(
        by=[
            min.defn(radius, p - lo),
            min.defn(radius, hi - p),
            abs.defn(left - p),
            abs.defn(right - p),
        ]
    )
    (left, right), _ = l.obtain(nearby)
    l.specialize(estimate, left, keep=True)
    l.specialize(estimate, right)

    # Either extremum would contradict the estimate if a were nonzero.
    maximum, minimum = extremum.children()
    l.cases(maximum, minimum)
    for bound in (maximum, minimum):
        l.specialize(bound, left, keep=True)
        l.specialize(bound, right)
        l.auto(
            by=[
                abs.defn(a),
                abs.defn(left - p),
                abs.defn(right - p),
                abs.defn(f[left] - f[p] - a * (left - p)),
                abs.defn(f[right] - f[p] - a * (right - p)),
            ]
        )


@Theorem(ForAll(x, has_deriv_at(Lambda(t, t * t), 2 * x, x)))
def has_deriv_at_sq(l):
    x = l.fix()
    l.rw(has_deriv_at_iff_remainder)
    eps = l.fix()
    l.intro()
    # The error is (y - x)^2, so delta = eps works.
    l.exists(eps)
    l.split()
    l.auto()
    y = l.fix()
    l.intro()
    l.beta()
    l.have(y * y - x * x - 2 * x * (y - x) == (y - x) * (y - x), by=[])
    l.auto(by=[abs.defn(y - x), abs.defn((y - x) * (y - x)), abs_mul(y - x, y - x)])
