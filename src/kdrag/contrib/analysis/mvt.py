"""Rolle's theorem and the mean value theorems."""

from kdrag import Theorem
from kdrag.smt import And, Consts, Exists, ForAll, Lambda, Reals
import kdrag.theories.real as real

from .compact import extreme_value_theorem, is_compact, is_compact_icc
from .cont import cont_on, cont_within_at_of_cont_at, cont_within_at_sub
from .deriv import (
    cont_at_of_has_deriv_at,
    deriv_eq_zero_of_interior_extremum,
    has_deriv_at,
    has_deriv_at_const_mul,
    has_deriv_at_id,
    has_deriv_at_sub_linear,
    has_deriv_at_unique,
)

f, df = Consts("f df", real.RFun)
x, lo, hi = Reals("x lo hi")


@Theorem(
    ForAll(
        [f, df, lo, hi],
        lo < hi,
        cont_on(f, real.icc(lo, hi)),
        ForAll(x, lo < x, x < hi, has_deriv_at(f, df[x], x)),
        f[lo] == f[hi],
        Exists(x, lo < x, x < hi, has_deriv_at(f, 0, x)),
    )
)
def rolle(l):
    """Abbott 5.3.1. Equal endpoint values force a zero derivative inside."""
    f, df, lo, hi = l.fixes()
    _, continuity, derivatives, _ = l.intros()
    domain = real.icc(lo, hi)
    compact = l.have(is_compact(domain), by=[is_compact_icc(lo, hi)])
    nonempty = l.have(Exists(x, domain[x]))
    l.exists(lo)
    l.auto(by=[real.icc.defn(lo, hi)])
    (low, high), extrema = l.obtain(
        l.specialize(extreme_value_theorem, f, domain, continuity, compact, nonempty)
    )
    _, _, bounds = l.andE(extrema)
    l.specialize(bounds, lo, keep=True)
    midpoint = (lo + hi) / 2
    l.specialize(bounds, midpoint, keep=True)

    # An extremum that differs from the common endpoint value is interior.
    # When both extrema have that value, the midpoint is also a minimum.
    l.cases(
        f[low] < f[lo],
        f[lo] < f[high],
        And(f[low] == f[lo], f[high] == f[lo]),
    )
    for point, bound in (
        (low, f[low] <= f[x]),
        (high, f[x] <= f[high]),
        (midpoint, f[midpoint] <= f[x]),
    ):
        l.have(And(lo < point, point < hi), by=[real.icc.defn(lo, hi)])
        l.have(ForAll(x, lo < x, x < hi, bound), by=[real.icc.defn(lo, hi)])
        l.specialize(derivatives, point)
        l.exists(point)
        l.auto(by=[deriv_eq_zero_of_interior_extremum(f, df[point], point, lo, hi)])


@Theorem(
    ForAll(
        [f, df, lo, hi],
        lo < hi,
        cont_on(f, real.icc(lo, hi)),
        ForAll(x, lo < x, x < hi, has_deriv_at(f, df[x], x)),
        Exists(x, lo < x, x < hi, has_deriv_at(f, (f[hi] - f[lo]) / (hi - lo), x)),
    )
)
def mean_value_theorem(l):
    """Abbott 5.3.2. Some interior derivative equals the secant slope."""
    f, df, lo, hi = l.fixes()
    ordered, continuous, derivatives = l.intros()
    domain = real.icc(lo, hi)
    slope = (f[hi] - f[lo]) / (hi - lo)
    line = Lambda(x, slope * x)
    g, dg = Lambda(x, f[x] - line[x]), Lambda(x, df[x] - slope)

    # Subtract a line with the secant slope to make the endpoint values equal.
    equal_endpoints = l.have(g[lo] == g[hi])
    l.beta()
    l.auto()
    continuous_g = l.have(cont_on(g, domain))
    l.unfold(cont_on)
    p = l.fix()
    l.intro()
    l.auto(
        by=[
            cont_on.defn(f, domain),
            has_deriv_at_id(p),
            has_deriv_at_const_mul(slope, Lambda(x, x), p, 1),
            cont_at_of_has_deriv_at(line, p, slope),
            cont_within_at_of_cont_at(line, domain, p),
            cont_within_at_sub(f, line, domain, p),
        ]
    )
    shifted = l.have(ForAll(x, lo < x, x < hi, has_deriv_at(g, dg[x], x)))
    p = l.fix()
    l.intros()
    l.specialize(derivatives, p)
    l.auto(by=[has_deriv_at_sub_linear(f, df[p], p, slope)])

    zero = l.specialize(
        rolle, g, dg, lo, hi, ordered, continuous_g, shifted, equal_endpoints
    )
    p, _ = l.obtain(zero)
    l.specialize(derivatives, p)
    l.have(
        has_deriv_at(g, df[p] - slope, p),
        by=[has_deriv_at_sub_linear(f, df[p], p, slope)],
    )
    l.exists(p)
    l.auto(by=[has_deriv_at_unique(g, p, df[p] - slope, 0)])
