"""Pointwise real limits, congruence, and continuity of compositions."""

from kdrag import Theorem
from kdrag.smt import And, Consts, Exists, Lambda, ForAll, RealVal, Reals, Store
from kdrag.theories.real import (
    RFun,
    abs,
    abs_div,
    abs_mul,
    abs_neg,
    abs_pos,
    abs_pos_iff,
    abs_triangle,
    cont_at,
    has_lim_at,
    min,
)

from kdrag.theories.real.cont import (
    cont_at_update_of_has_lim_at,
    has_lim_at_of_cont_at_update,
)

f, g = Consts("f g", RFun)
x, p, L, M, c = Reals("x p L M c")


@Theorem(ForAll([f, p, L, M], has_lim_at(f, p, L), has_lim_at(f, p, M), L == M))
def has_lim_at_unique(l):
    f, p, L, M = l.fixes()
    l.unfold(has_lim_at)
    hL, hM = l.intros()
    l.contra()
    eps = abs(L - M) / 2
    positive = l.have(RealVal(0) < eps, by=[abs.defn])
    d1, _ = l.obtain(l.specialize(hL, eps, positive))
    d2, _ = l.obtain(l.specialize(hM, eps, positive))
    # A common point must be near p but different from p.
    x = p + min(d1, d2) / 2
    l.have(
        And(0 < abs(x - p), abs(x - p) < d1, abs(x - p) < d2),
        by=[abs.defn, min.defn],
    )
    l.have(abs(f[x] - L) < eps, by=[])
    l.have(abs(f[x] - M) < eps, by=[])
    l.auto(by=[abs.defn])


@Theorem(
    ForAll(
        [f, g, p, L],
        ForAll([x], x != p, f[x] == g[x]),
        has_lim_at(f, p, L),
        has_lim_at(g, p, L),
    )
)
def has_lim_at_congr(l):
    """A limit at p only depends on values away from p."""
    f, g, p, L = l.fixes()
    l.intros()
    # Redefine both at p as L: the updated functions are equal, and a limit at p
    # is continuity of the update at p.
    l.have(cont_at(Store(f, p, L), p), by=[cont_at_update_of_has_lim_at(f, p, L)])
    l.have(Store(f, p, L) == Store(g, p, L), by=[])
    l.auto(by=[has_lim_at_of_cont_at_update(g, p, L)])


@Theorem(ForAll([c, p], has_lim_at(Lambda(x, c), p, c)))
def has_lim_at_const(l):
    l.fixes()
    l.auto(by=[has_lim_at.defn, abs.defn])


@Theorem(
    ForAll([f, g, p], cont_at(f, p), cont_at(g, f[p]), cont_at(Lambda(x, g[f[x]]), p))
)
def cont_at_comp(l):
    f, g, p = l.fixes()
    l.unfold(cont_at)
    hf, hg = l.intros()
    eps = l.fix()
    l.intro()
    d, y = Reals("delta y")
    # g's delta at f(p) for eps ...
    hg = l.specialize(hg, eps)
    w = l.have(
        Exists(d, d > 0, ForAll(y, abs(f[p] - y) < d, abs(g[f[p]] - g[y]) < eps)), by=[]
    )
    l.clear(hg)
    d1, _ = l.obtain(w)
    # ... is the target for f's delta at p.
    hf = l.specialize(hf, d1)
    w = l.have(
        Exists(d, d > 0, ForAll(y, abs(p - y) < d, abs(f[p] - f[y]) < d1)), by=[]
    )
    l.clear(hf)
    d2, _ = l.obtain(w)
    l.exists(d2)
    l.auto()


@Theorem(ForAll([p], has_lim_at(Lambda(x, x), p, p)))
def has_lim_at_id(l):
    l.fix()
    l.unfold(has_lim_at)
    eps = l.fix()
    l.intro()
    l.exists(eps)
    l.auto(by=[abs.defn])


eps, delta = Reals("eps delta")


@Theorem(
    ForAll(
        [f, p, L, eps],
        has_lim_at(f, p, L),
        RealVal(0) < eps,
        Exists(
            delta,
            delta > 0,
            ForAll(x, RealVal(0) < abs(x - p), abs(x - p) < delta, abs(f[x] - L) < eps),
        ),
    )
)
def exists_limit_radius(l):
    f, p, L, eps = l.fixes()
    l.unfold(has_lim_at)
    limit, positive = l.intros()
    l.specialize(limit, eps, positive)
    l.assumption()


u, v, a, b = Reals("u v a b")


@Theorem(
    ForAll(
        [u, v, a, b, eps],
        b != 0,
        eps > 0,
        abs(u - a) < eps * abs(b) / 4,
        abs(v - b) < min(abs(b) / 2, eps * abs(b) * abs(b) / (4 * (abs(a) + 1))),
        abs(u / v - a / b) < eps,
    )
)
def div_error_at(l):
    u, v, a, b, eps = l.fixes()
    l.intros()
    B, A = abs(b), abs(a)
    e1, e2 = abs(u - a), abs(v - b)
    l.have(B > 0, by=[abs_pos_iff(b)])
    l.have(e2 < B / 2, by=[min.defn(B / 2, eps * B * B / (4 * (A + 1)))])
    l.have(abs(v) > B / 2, by=[abs_triangle(b, RealVal(0), v), abs_neg(v - b)])
    l.have(v != 0, by=[abs_pos_iff(v)])
    l.have(u / v - a / b == ((u - a) * b - a * (v - b)) / (v * b), by=[])
    numerator = (u - a) * b - a * (v - b)
    l.have(
        abs(numerator) <= e1 * B + A * e2,
        by=[
            abs_triangle((u - a) * b, a * (v - b), RealVal(0)),
            abs_mul(u - a, b),
            abs_mul(a, v - b),
            abs_neg(a * (v - b)),
        ],
    )
    l.have(e1 * B < eps * B * B / 4, by=[])
    l.have(
        A * e2 <= eps * B * B / 4,
        by=[abs_pos(a), min.defn(B / 2, eps * B * B / (4 * (A + 1)))],
    )
    l.have(abs(v * b) == abs(v) * B, by=[abs_mul(v, b)])
    l.auto(by=[abs_div(numerator, v * b)])


@Theorem(
    ForAll(
        [f, g, p, L, M],
        has_lim_at(f, p, L),
        has_lim_at(g, p, M),
        M != 0,
        has_lim_at(Lambda(x, f[x] / g[x]), p, L / M),
    )
)
def has_lim_at_div(l):
    f, g, p, L, M = l.fixes()
    hf = l.intro()
    hg = l.intro()
    l.intro()
    l.unfold(has_lim_at)
    eps = l.fix()
    l.intro()
    B, A = abs(M), abs(L)
    ea = eps * B / 4
    eb = min(B / 2, eps * B * B / (4 * (A + 1)))
    l.have(B > 0, by=[abs_pos_iff(M)])
    pa = l.have(RealVal(0) < ea, by=[])
    pb = l.have(
        RealVal(0) < eb, by=[abs_pos(L), min.defn(B / 2, eps * B * B / (4 * (A + 1)))]
    )
    da, near_f = l.obtain(l.specialize(exists_limit_radius, f, p, L, ea, hf, pa))
    db, near_g = l.obtain(l.specialize(exists_limit_radius, g, p, M, eb, hg, pb))
    l.exists(min(da, db))
    l.split()
    l.auto(by=[min.defn(da, db)])
    z = l.fix()
    positive, close = l.intros()
    fa = l.have(abs(z - p) < da, by=[min.defn(da, db)])
    gb = l.have(abs(z - p) < db, by=[min.defn(da, db)])
    l.split(at=near_f)
    _, near_f = near_f.children()
    l.specialize(near_f, z, positive, fa)
    l.split(at=near_g)
    _, near_g = near_g.children()
    l.specialize(near_g, z, positive, gb)
    l.auto(by=[div_error_at(f[z], g[z], L, M, eps)])
