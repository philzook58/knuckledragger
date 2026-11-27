"""The intermediate value property of derivatives."""

from kdrag import Theorem
from kdrag.smt import And, Consts, Exists, ForAll, If, Implies, Lambda, Or, Reals
import kdrag.theories.real as real

from .compact import extreme_value_theorem, is_compact, is_compact_icc
from .cont import cont_on, cont_within_at_of_cont_at
from .deriv import (
    cont_at_of_has_deriv_at,
    deriv_eq_zero_of_interior_extremum,
    has_deriv_at,
    has_deriv_at_iff_remainder,
    has_deriv_at_sub_linear,
)

f, df = Consts("f df", real.RFun)
x, p, q, d, lo, hi, level = Reals("x p q d lo hi level")


def _between(p, x, q):
    return Or(And(p < x, x < q), And(q < x, x < p))


def _nearby_value(f, d, p, q, x):
    return And(
        _between(p, x, q),
        Implies(d * (q - p) < 0, f[x] < f[p]),
        Implies(d * (q - p) > 0, f[p] < f[x]),
    )


@Theorem(
    ForAll(
        [f, d, p, q],
        has_deriv_at(f, d, p),
        d != 0,
        p != q,
        Exists(x, _nearby_value(f, d, p, q, x)),
    )
)
def _exists_nearby_value_in_derivative_direction(l):
    f, d, p, q = l.fixes()
    l.rw(has_deriv_at_iff_remainder(f, d, p))
    differentiable, _, _ = l.intros()
    error = real.abs(d) / 2
    positive = l.have(error > 0, by=[real.abs.defn(d)])
    radius, witness = l.obtain(l.specialize(differentiable, error, positive))
    _, estimate = l.andE(witness)

    # Move a short distance toward q, staying strictly between p and q.
    extent = real.abs(q - p)
    step = real.min(radius, extent) / 2
    nearby = l.have(Exists(x, _between(p, x, q), real.abs(x - p) < radius))
    point = p + If(p < q, step, -step)
    l.exists(point)
    l.auto(
        by=[
            real.abs.defn(q - p),
            real.min.defn(radius, extent),
            real.abs.defn(point - p),
        ]
    )
    point, _ = l.obtain(nearby)
    l.specialize(estimate, point)
    l.exists(point)
    l.auto(
        by=[
            real.abs.defn(d),
            real.abs.defn(point - p),
            real.abs.defn(f[point] - f[p] - d * (point - p)),
        ]
    )


def _derivatives_on(f, df, domain):
    return ForAll(x, domain[x], has_deriv_at(f, df[x], x))


@Theorem(
    ForAll(
        [f, df, lo, hi],
        lo < hi,
        _derivatives_on(f, df, real.icc(lo, hi)),
        Or(And(df[lo] < 0, 0 < df[hi]), And(df[hi] < 0, 0 < df[lo])),
        Exists(x, lo < x, x < hi, df[x] == 0),
    )
)
def _exists_zero_of_opposite_endpoint_derivatives(l):
    f, df, lo, hi = l.fixes()
    _, derivatives, signs = l.intros()
    domain = real.icc(lo, hi)
    continuity = l.have(cont_on(f, domain))
    l.unfold(cont_on)
    p = l.fix()
    l.intro()
    l.specialize(derivatives, p)
    l.auto(
        by=[
            cont_at_of_has_deriv_at(f, p, df[p]),
            cont_within_at_of_cont_at(f, domain, p),
        ]
    )
    compact = l.have(is_compact(domain), by=[is_compact_icc(lo, hi)])
    nonempty = l.have(Exists(x, domain[x]))
    l.exists(lo)
    l.auto(by=[real.icc.defn(lo, hi)])
    (low_point, high_point), extrema = l.obtain(
        l.specialize(extreme_value_theorem, f, domain, continuity, compact, nonempty)
    )
    _, _, bounds = l.andE(extrema)

    endpoints = l.have(And(domain[lo], domain[hi]), by=[real.icc.defn(lo, hi)])
    left_mem, right_mem = l.andE(endpoints)
    l.specialize(derivatives, lo, left_mem, keep=True)
    l.specialize(derivatives, hi, right_mem, keep=True)
    left_nearby = l.have(
        Exists(x, _nearby_value(f, df[lo], lo, hi, x)),
        by=[_exists_nearby_value_in_derivative_direction(f, df[lo], lo, hi)],
    )
    right_nearby = l.have(
        Exists(x, _nearby_value(f, df[hi], hi, lo, x)),
        by=[_exists_nearby_value_in_derivative_direction(f, df[hi], hi, lo)],
    )
    left, _ = l.obtain(left_nearby)
    right, _ = l.obtain(right_nearby)
    l.specialize(bounds, left, keep=True)
    l.specialize(bounds, right, keep=True)

    # Negative-to-positive slopes force the minimum into the interior.
    # Positive-to-negative slopes do the same for the maximum.
    rising, falling = signs.children()
    l.cases(rising, falling)
    for point, is_extremum in (
        (low_point, ForAll(x, lo < x, x < hi, f[low_point] <= f[x])),
        (high_point, ForAll(x, lo < x, x < hi, f[x] <= f[high_point])),
    ):
        l.have(And(lo < point, point < hi), by=[real.icc.defn(lo, hi)])
        l.have(is_extremum, by=[real.icc.defn(lo, hi)])
        l.specialize(derivatives, point)
        l.exists(point)
        l.auto(by=[deriv_eq_zero_of_interior_extremum(f, df[point], point, lo, hi)])


@Theorem(
    ForAll(
        [f, df, lo, hi, level],
        lo < hi,
        _derivatives_on(f, df, real.icc(lo, hi)),
        _between(df[lo], level, df[hi]),
        Exists(x, lo < x, x < hi, has_deriv_at(f, level, x)),
    )
)
def darboux(l):
    """Abbott 5.2.7. A derivative takes every value between its endpoint values."""
    f, df, lo, hi, level = l.fixes()
    _, derivatives, _ = l.intros()
    domain = real.icc(lo, hi)
    g, dg = Lambda(x, f[x] - level * x), Lambda(x, df[x] - level)
    l.have(_derivatives_on(g, dg, domain))
    p = l.fix()
    member = l.intro()
    l.specialize(derivatives, p, member)
    l.auto(by=[has_deriv_at_sub_linear(f, df[p], p, level)])
    zero = l.have(
        Exists(x, lo < x, x < hi, dg[x] == 0),
        by=[_exists_zero_of_opposite_endpoint_derivatives(g, dg, lo, hi)],
    )
    c, _ = l.obtain(zero)
    l.specialize(derivatives, c)
    l.exists(c)
    l.auto(by=[real.icc.defn(lo, hi)])
