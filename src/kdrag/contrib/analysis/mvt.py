"""Rolle's theorem and the mean value theorems."""

from kdrag import Theorem
from kdrag.smt import And, Consts, Exists, ForAll, Reals
import kdrag.theories.real as real

from .compact import extreme_value_theorem, is_compact, is_compact_icc
from .cont import cont_on
from .deriv import deriv_eq_zero_of_interior_extremum, has_deriv_at

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
