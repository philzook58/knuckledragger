"""Finite 0/0 limits and the secant step of L'Hôpital's rule."""

from kdrag import Theorem
from kdrag.contrib.analysis.cont import exists_limit_radius, has_lim_at_div
from kdrag.contrib.analysis.deriv import has_deriv_at, quot
from kdrag.smt import Consts, Exists, ForAll, Lambda, RealVal, Reals
from kdrag.theories.real import RFun, abs, abs_pos_iff, has_lim_at, min

f, g, df, dg = Consts("f g df dg", RFun)
p, x, z, a, b, limit, radius = Reals("p x z a b limit radius")


@Theorem(
    ForAll(
        [f, g, p, a, b],
        f[p] == 0,
        g[p] == 0,
        has_deriv_at(f, a, p),
        has_deriv_at(g, b, p),
        b != 0,
        has_lim_at(Lambda(x, f[x] / g[x]), p, a / b),
    )
)
def lhopital_zero_of_has_deriv_at(l):
    """The finite 0/0 case for functions differentiable at the base point."""
    f, g, p, a, b = l.fixes()
    l.intros()
    qf, qg = quot(f, p), quot(g, p)
    l.have(has_lim_at(qf, p, a), by=[has_deriv_at.defn(f, a, p)])
    hg = l.have(has_lim_at(qg, p, b), by=[has_deriv_at.defn(g, b, p)])
    divided = Lambda(x, qf[x] / qg[x])
    hl = l.have(has_lim_at(divided, p, a / b), by=[has_lim_at_div(qf, qg, p, a, b)])
    l.unfold(has_lim_at)
    eps = l.fix()
    positive = l.intro()
    half = l.have(RealVal(0) < abs(b) / 2, by=[abs_pos_iff(b)])
    dg, near_g = l.obtain(
        l.specialize(exists_limit_radius, qg, p, b, abs(b) / 2, hg, half)
    )
    dq, near_q = l.obtain(
        l.specialize(exists_limit_radius, divided, p, a / b, eps, hl, positive)
    )
    l.exists(min(dg, dq))
    l.split()
    l.auto(by=[min.defn(dg, dq)])
    z = l.fix()
    away, _ = l.intros()
    close_g = l.have(abs(z - p) < dg, by=[min.defn(dg, dq)])
    close_q = l.have(abs(z - p) < dq, by=[min.defn(dg, dq)])
    l.split(at=near_g)
    _, near_g = near_g.children()
    l.specialize(near_g, z, away, close_g)
    l.split(at=near_q)
    _, near_q = near_q.children()
    l.specialize(near_q, z, away, close_q)
    l.have(z != p, by=[abs.defn(z - p)])
    l.have(qg[z] != 0, by=[abs.defn(qg[z] - b), abs.defn(b)])
    l.have(g[z] != 0, by=[])
    l.have(qf[z] == f[z] / (z - p), by=[])
    l.have(qg[z] == g[z] / (z - p), by=[])
    l.have(qf[z] / qg[z] == f[z] / g[z], by=[])
    # Match the pointwise quotient in the last equality.
    l.beta()
    l.auto()


@Theorem(
    ForAll(
        [f, g, df, dg, p, limit, radius],
        radius > 0,
        has_lim_at(Lambda(x, df[x] / dg[x]), p, limit),
        ForAll(
            x,
            RealVal(0) < abs(x - p),
            abs(x - p) < radius,
            Exists(
                z,
                RealVal(0) < abs(z - p),
                abs(z - p) <= abs(x - p),
                f[x] / g[x] == df[z] / dg[z],
            ),
        ),
        has_lim_at(Lambda(x, f[x] / g[x]), p, limit),
    )
)
def lhopital_of_secant(l):
    """Transfer a finite limit through the secant identity from Cauchy's mean value theorem."""
    f, g, df, dg, p, limit, radius = l.fixes()
    l.intro()
    derivative_limit = l.intro()
    secant = l.intro()
    l.unfold(has_lim_at)
    eps = l.fix()
    positive = l.intro()
    derivative_ratio = Lambda(x, df[x] / dg[x])
    cutoff, near = l.obtain(
        l.specialize(
            exists_limit_radius,
            derivative_ratio,
            p,
            limit,
            eps,
            derivative_limit,
            positive,
        )
    )
    l.exists(min(radius, cutoff))
    l.split()
    l.auto(by=[min.defn(radius, cutoff)])
    point = l.fix()
    away, _ = l.intros()
    within = l.have(abs(point - p) < radius, by=[min.defn(radius, cutoff)])
    z, _ = l.obtain(l.specialize(secant, point, away, within))
    away_z = l.have(RealVal(0) < abs(z - p), by=[])
    close_z = l.have(abs(z - p) < cutoff, by=[min.defn(radius, cutoff)])
    l.split(at=near)
    _, near = near.children()
    l.specialize(near, z, away_z, close_z)
    l.auto()
