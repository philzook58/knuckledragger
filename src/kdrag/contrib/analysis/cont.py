"""Exploratory uniqueness theorem for pointwise real limits."""

from kdrag import Theorem
from kdrag.smt import And, Consts, ForAll, RealVal, Reals
from kdrag.theories.real import RFun, abs, has_lim_at, min

f, g = Consts("f g", RFun)
x, p, L, M = Reals("x p L M")


@Theorem(ForAll([f, p, L, M], has_lim_at(f, p, L), has_lim_at(f, p, M), L == M))
def has_lim_at_unique(l):
    f, p, L, M = l.fixes()
    l.unfold(has_lim_at)
    hL, hM = l.intros()
    l.contra()
    eps = abs(L - M) / 2
    positive = l.have(RealVal(0) < eps, by=[abs.defn])
    d1 = l.obtain(l.specialize(hL, eps, positive))
    d2 = l.obtain(l.specialize(hM, eps, positive))
    # A common point must be near p but different from p.
    x = p + min(d1, d2) / 2
    l.have(
        And(0 < abs(x - p), abs(x - p) < d1, abs(x - p) < d2),
        by=[abs.defn, min.defn],
    )
    l.have(abs(f[x] - L) < eps, by=[])
    l.have(abs(f[x] - M) < eps, by=[])
    l.auto(by=[abs.defn])
