"""Pointwise real limits, congruence, and continuity of compositions."""

from kdrag import Theorem
from kdrag.smt import And, Consts, Exists, Lambda, ForAll, RealVal, Reals, Store
from kdrag.theories.real import RFun, abs, cont_at, has_lim_at, min

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
