"""Derivative rules for `has_diff_at`, the limit of the difference quotient.

Linearity follows from the limit rules in `cont`, using that a limit at p ignores
the value at p (the quotient is 0/0 there). The chain rule goes through
Carathéodory's characterisation, which avoids dividing by f(x) - f(p).
"""

from kdrag import Theorem, define, prove
from kdrag.smt import Consts, Exists, ForAll, Lambda, Reals, RealVal, Store

from kdrag.theories.real import RFun, abs, cont_at, fmul, has_lim_at
from kdrag.theories.real.cont import (
    has_lim_at_of_cont_at,
    cont_at_update_of_has_lim_at,
    has_lim_at_add,
    has_lim_at_mul,
    has_lim_at_of_cont_at_update,
)

f, g = Consts("f g", RFun)
x, p, L, a, b, c = Reals("x p L a b c")


# Keep this exploratory definition separate from real.has_diff_at until reviewed.
has_diff_at = define(
    "analysis.has_diff_at",
    [f, p, L],
    has_lim_at(Lambda(x, (f[x] - f[p]) / (x - p)), p, L),
)


def quot(f, p):
    """The difference quotient of f at p."""
    return Lambda(x, (f[x] - f[p]) / (x - p))


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


@Theorem(ForAll([c, p], has_diff_at(Lambda(x, c), p, 0)))
def has_diff_at_const(l):
    c, p = l.fixes()
    l.unfold(has_diff_at)
    # The quotient (c - c) / (x - p) is 0 away from p.
    zero = Lambda(x, RealVal(0))
    l.auto(
        by=[has_lim_at_congr(zero, quot(Lambda(x, c), p), p, 0), has_lim_at_const(0, p)]
    )


@Theorem(ForAll([p], has_diff_at(Lambda(x, x), p, 1)))
def has_diff_at_id(l):
    p = l.fix()
    l.unfold(has_diff_at)
    # The quotient (x - p) / (x - p) is 1 away from p.
    one = Lambda(x, RealVal(1))
    l.auto(
        by=[has_lim_at_congr(one, quot(Lambda(x, x), p), p, 1), has_lim_at_const(1, p)]
    )


@Theorem(
    ForAll(
        [f, g, p, a, b],
        has_diff_at(f, p, a),
        has_diff_at(g, p, b),
        has_diff_at(f + g, p, a + b),
    )
)
def has_diff_at_add(l):
    f, g, p, a, b = l.fixes()
    l.intros()
    l.unfold(has_diff_at)
    qf, qg = quot(f, p), quot(g, p)
    l.have(has_lim_at(qf, p, a), by=[has_diff_at.defn(f, p, a)])
    l.have(has_lim_at(qg, p, b), by=[has_diff_at.defn(g, p, b)])
    l.have(has_lim_at(qf + qg, p, a + b), by=[has_lim_at_add(qf, qg, p, a, b)])
    # The quotient of f + g is the sum of the quotients away from p.
    l.auto(by=[has_lim_at_congr(qf + qg, quot(f + g, p), p, a + b)])


@Theorem(
    ForAll(
        [c, f, p, a],
        has_diff_at(f, p, a),
        has_diff_at(Lambda(x, c * f[x]), p, c * a),
    )
)
def has_diff_at_const_mul(l):
    c, f, p, a = l.fixes()
    l.intro()
    l.unfold(has_diff_at)
    qf, cf = quot(f, p), Lambda(x, c)
    l.have(has_lim_at(qf, p, a), by=[has_diff_at.defn(f, p, a)])
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


@Theorem(ForAll([f, p, a], has_diff_at(f, p, a), cont_at(slope(f, p, a), p)))
def cont_at_slope_of_has_diff_at(l):
    f, p, a = l.fixes()
    l.intro()
    l.auto(
        by=[has_diff_at.defn(f, p, a), cont_at_update_of_has_lim_at(quot(f, p), p, a)]
    )


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
    d1 = l.obtain(w)
    # ... is the target for f's delta at p.
    hf = l.specialize(hf, d1)
    w = l.have(
        Exists(d, d > 0, ForAll(y, abs(p - y) < d, abs(f[p] - f[y]) < d1)), by=[]
    )
    l.clear(hf)
    d2 = l.obtain(w)
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


@Theorem(ForAll([f, p, a], has_diff_at(f, p, a), cont_at(f, p)))
def cont_at_of_has_diff_at(l):
    """A differentiable function is continuous."""
    f, p, a = l.fixes()
    l.intro()
    s, lin, fp = slope(f, p, a), Lambda(x, x - p), Lambda(x, f[p])
    # The slope tends to a and x - p tends to 0 ...
    l.have(
        has_lim_at(s, p, a),
        by=[has_lim_at_of_cont_at(s, p), cont_at_slope_of_has_diff_at(f, p, a)],
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
        has_diff_at(f, p, a),
        has_diff_at(g, f[p], b),
        has_diff_at(Lambda(x, g[f[x]]), p, b * a),
    )
)
def has_diff_at_comp(l):
    """The chain rule."""
    f, g, p, a, b = l.fixes()
    l.intros()
    sf, sg = slope(f, p, a), slope(g, f[p], b)
    sgf = Lambda(x, sg[f[x]])
    # sg(f x) tends to sg(f p) = b, since f is continuous and sg continuous at f(p).
    l.have(cont_at(f, p), by=[cont_at_of_has_diff_at(f, p, a)])
    l.have(cont_at(sg, f[p]), by=[cont_at_slope_of_has_diff_at(g, f[p], b)])
    l.have(cont_at(sgf, p), by=[cont_at_comp(f, sg, p)])
    l.have(has_lim_at(sgf, p, b), by=[has_lim_at_of_cont_at(sgf, p)])
    # sf tends to a.
    l.have(
        has_lim_at(sf, p, a),
        by=[has_lim_at_of_cont_at(sf, p), cont_at_slope_of_has_diff_at(f, p, a)],
    )
    l.have(has_lim_at(sgf * sf, p, b * a), by=[has_lim_at_mul(sgf, sf, p, b, a)])
    # Prove the pointwise identity before transporting the product limit.
    target = quot(Lambda(x, g[f[x]]), p)
    l.have(ForAll(x, x != p, (sgf * sf)[x] == target[x]))
    z = l.fix()
    l.intro()
    l.auto(by=[fmul.defn(sgf, sf), quot_comp_eq(f, g, p, a, b, z)])
    l.unfold(has_diff_at)
    l.auto(by=[has_lim_at_congr(sgf * sf, target, p, b * a)])
