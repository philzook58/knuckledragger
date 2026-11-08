"""Continuity and limit lemmas for real functions.

Prove pointwise closure first, then derive global continuity and limit rules.
"""

from kdrag import FreshVars, Theorem, prove
from kdrag.smt import And, Consts, ForAll, Implies, Lambda, RealSort, Reals, Store
from kdrag.theories.real import (
    RFun,
    abs,
    cont_at,
    fadd,
    fmul,
    has_lim_at,
    is_cont,
    min,
)

f, g = Consts("f g", RFun)
x, p, L, M = Reals("x p L M")

cont_at_of_is_cont = prove(
    ForAll([f, x], Implies(is_cont(f), cont_at(f, x))),
    by=[is_cont.defn],
)


@Theorem(ForAll([f, x], Implies(cont_at(f, x), has_lim_at(f, x, f[x]))))
def has_lim_at_of_cont_at(l):
    l.fixes()
    l.unfold(cont_at, has_lim_at)
    continuity = l.intros()
    eps = l.fix()
    l.intros()
    # Reuse continuity's delta for the punctured neighborhood.
    delta = l.obtain(l.forward(l.specialize(continuity, eps)))
    l.exists(delta)
    l.auto(by=[abs.defn])


@Theorem(
    ForAll([f, g, p], Implies(cont_at(f, p), Implies(cont_at(g, p), cont_at(f + g, p))))
)
def cont_at_add(l):
    l.fixes()
    l.unfold(cont_at)
    hf, hg = l.intros(), l.intros()
    l.unfold(fadd)
    eps = l.fix()
    l.intros()
    # Each summand gets half the error budget.
    d1 = l.obtain(l.forward(l.specialize(hf, eps / 2)))
    d2 = l.obtain(l.forward(l.specialize(hg, eps / 2)))
    l.exists(min(d1, d2))
    l.auto(by=[abs.defn, min.defn])


@Theorem(
    ForAll([f, g, p], Implies(cont_at(f, p), Implies(cont_at(g, p), cont_at(f * g, p))))
)
def cont_at_mul(l):
    f, g, p = l.fixes()
    l.unfold(cont_at)
    hf, hg = l.intros(), l.intros()
    l.unfold(fmul)
    eps = l.fix()
    l.intros()
    # Keep both errors below one and control the product error.
    eta = min(1, eps / (2 * (abs(f[p]) + abs(g[p]) + 1)))
    l.have(eta > 0, by=[abs.defn, min.defn])
    d1 = l.obtain(l.forward(l.specialize(hf, eta)))
    d2 = l.obtain(l.forward(l.specialize(hg, eta)))
    l.exists(min(d1, d2))
    l.split()
    l.auto(by=[min.defn])
    y = l.fix()
    l.intros()
    l.have(And(abs(p - y) < d1, abs(p - y) < d2), by=[min.defn])
    l.have(abs(f[p] - f[y]) < eta, by=[])
    l.have(abs(g[p] - g[y]) < eta, by=[])
    l.have(
        And(eta <= 1, 2 * eta * (abs(f[p]) + abs(g[p]) + 1) <= eps),
        by=[abs.defn, min.defn],
    )
    l.auto(by=[abs.defn])


is_cont_add = prove(
    ForAll([f, g], Implies(is_cont(f), Implies(is_cont(g), is_cont(f + g)))),
    by=[is_cont.defn, cont_at_add],
)

is_cont_mul = prove(
    ForAll([f, g], Implies(is_cont(f), Implies(is_cont(g), is_cont(f * g)))),
    by=[is_cont.defn, cont_at_mul],
)


# Updating the value at p turns a punctured limit into continuity at p.
@Theorem(ForAll([f, p, L], Implies(has_lim_at(f, p, L), cont_at(Store(f, p, L), p))))
def cont_at_update_of_has_lim_at(l):
    l.fixes()
    l.unfold(has_lim_at, cont_at)
    limit = l.intros()
    eps = l.fix()
    l.intros()
    delta = l.obtain(l.forward(l.specialize(limit, eps)))
    l.exists(delta)
    l.auto(by=[abs.defn])


@Theorem(ForAll([f, p, L], Implies(cont_at(Store(f, p, L), p), has_lim_at(f, p, L))))
def has_lim_at_of_cont_at_update(l):
    l.fixes()
    l.unfold(cont_at, has_lim_at)
    continuity = l.intros()
    eps = l.fix()
    l.intros()
    delta = l.obtain(l.forward(l.specialize(continuity, eps)))
    l.exists(delta)
    l.auto(by=[abs.defn])


@Theorem(
    ForAll(
        [f, g, p, L, M],
        Implies(
            has_lim_at(f, p, L),
            Implies(has_lim_at(g, p, M), has_lim_at(f + g, p, L + M)),
        ),
    )
)
def has_lim_at_add(l):
    f, g, p, L, M = l.fixes()
    l.intros()
    l.intros()
    f1, g1 = Store(f, p, L), Store(g, p, M)
    l.have(cont_at(f1, p), by=[cont_at_update_of_has_lim_at(f, p, L)])
    l.have(cont_at(g1, p), by=[cont_at_update_of_has_lim_at(g, p, M)])
    l.have(cont_at(f1 + g1, p), by=[cont_at_add(f1, g1, p)])
    l.have(f1 + g1 == Store(f + g, p, L + M), by=[fadd.defn(f1, g1), fadd.defn(f, g)])
    l.auto(by=[has_lim_at_of_cont_at_update(f + g, p, L + M)])


@Theorem(
    ForAll(
        [f, g, p, L, M],
        Implies(
            has_lim_at(f, p, L),
            Implies(has_lim_at(g, p, M), has_lim_at(f * g, p, L * M)),
        ),
    )
)
def has_lim_at_mul(l):
    f, g, p, L, M = l.fixes()
    l.intros()
    l.intros()
    f1, g1 = Store(f, p, L), Store(g, p, M)
    l.have(cont_at(f1, p), by=[cont_at_update_of_has_lim_at(f, p, L)])
    l.have(cont_at(g1, p), by=[cont_at_update_of_has_lim_at(g, p, M)])
    l.have(cont_at(f1 * g1, p), by=[cont_at_mul(f1, g1, p)])
    l.have(f1 * g1 == Store(f * g, p, L * M), by=[fmul.defn(f1, g1), fmul.defn(f, g)])
    l.auto(by=[has_lim_at_of_cont_at_update(f * g, p, L * M)])


a, p = FreshVars("a p", RealSort())


@Theorem(ForAll(a, is_cont(Lambda(x, a))))
def continuous_const(l):
    l.unfold(is_cont).unfold(cont_at).unfold(abs).auto()


@Theorem(is_cont(Lambda(x, x)))
def continuous_id(l):
    l.unfold(is_cont).unfold(cont_at).unfold(abs).auto()


@Theorem(ForAll(a, is_cont(Lambda(x, x + a))))
def continuous_add_const(l):
    a = l.fix()
    identity, constant = Lambda(x, x), Lambda(x, a)
    l.auto(
        by=[
            fadd.defn(identity, constant),
            is_cont_add(identity, constant)(continuous_id, continuous_const(a)),
        ]
    )


@Theorem(is_cont(Lambda(x, x * x)))
def continuous_sq(l):
    identity = Lambda(x, x)
    l.auto(
        by=[
            fmul.defn(identity, identity),
            is_cont_mul(identity, identity)(continuous_id, continuous_id),
        ]
    )


@Theorem(is_cont(Lambda(x, x * x * x)))
def continuous_cube(l):
    square, identity = Lambda(x, x * x), Lambda(x, x)
    l.auto(
        by=[
            fmul.defn(square, identity),
            is_cont_mul(square, identity)(continuous_sq, continuous_id),
        ]
    )


@Theorem(is_cont(Lambda(x, abs(x))))
def continuous_abs(l):
    l.unfold(is_cont).unfold(cont_at).unfold(abs).auto()


# Apply the bridge lemmas directly, then generalize the arbitrary parameters.
continuous_at_const = cont_at_of_is_cont(Lambda(x, a), p)(continuous_const(a)).forall(
    [a, p]
)
continuous_at_id = cont_at_of_is_cont(Lambda(x, x), p)(continuous_id).forall([p])
continuous_at_add_const = cont_at_of_is_cont(Lambda(x, x + a), p)(
    continuous_add_const(a)
).forall([a, p])
continuous_at_sq = cont_at_of_is_cont(Lambda(x, x * x), p)(continuous_sq).forall([p])
continuous_at_cube = cont_at_of_is_cont(Lambda(x, x * x * x), p)(
    continuous_cube
).forall([p])
continuous_at_abs = cont_at_of_is_cont(Lambda(x, abs(x)), p)(continuous_abs).forall([p])

# A continuous function tends to its value at the point.
has_lim_at_const = has_lim_at_of_cont_at(Lambda(x, a), p)(
    continuous_at_const(a, p)
).forall([a, p])
has_lim_at_id = has_lim_at_of_cont_at(Lambda(x, x), p)(continuous_at_id(p)).forall([p])
has_lim_at_add_const = has_lim_at_of_cont_at(Lambda(x, x + a), p)(
    continuous_at_add_const(a, p)
).forall([a, p])
has_lim_at_sq = has_lim_at_of_cont_at(Lambda(x, x * x), p)(continuous_at_sq(p)).forall(
    [p]
)
has_lim_at_cube = has_lim_at_of_cont_at(Lambda(x, x * x * x), p)(
    continuous_at_cube(p)
).forall([p])
has_lim_at_abs = has_lim_at_of_cont_at(Lambda(x, abs(x)), p)(
    continuous_at_abs(p)
).forall([p])
