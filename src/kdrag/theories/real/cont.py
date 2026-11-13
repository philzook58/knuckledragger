"""Continuity and limit lemmas for real functions.

Prove pointwise closure first, then derive global continuity and limit rules.
"""

from kdrag import FreshVars, Theorem, exact, prove
from kdrag.smt import (
    And,
    Consts,
    Exists,
    ForAll,
    Lambda,
    RealSort,
    RealVal,
    Reals,
    Store,
)
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
    ForAll([f, x], is_cont(f), cont_at(f, x)),
    by=[is_cont.defn],
)


@Theorem(ForAll([f, x], cont_at(f, x), has_lim_at(f, x, f[x])))
def has_lim_at_of_cont_at(l):
    f, x = l.fixes()
    l.unfold(cont_at, has_lim_at)
    continuity = l.intros()
    eps = l.fix()
    l.intros()
    # Reuse continuity's delta for the punctured neighborhood.
    continuity = l.specialize(continuity, eps)
    d, y = Reals("delta y")
    witness = l.have(
        Exists(d, d > 0, ForAll(y, abs(x - y) < d, abs(f[x] - f[y]) < eps)), by=[]
    )
    l.clear(continuity)
    delta = l.obtain(witness)
    l.exists(delta)
    l.auto(by=[abs.defn])


@Theorem(ForAll([f, g, p], cont_at(f, p), cont_at(g, p), cont_at(f + g, p)))
def cont_at_add(l):
    f, g, p = l.fixes()
    l.unfold(cont_at)
    hf, hg = l.intros(), l.intros()
    l.unfold(fadd)
    eps = l.fix()
    l.intros()
    # Each summand gets half the error budget.
    hf = l.specialize(hf, eps / 2)
    hg = l.specialize(hg, eps / 2)
    d, y = Reals("delta y")
    witness_f = l.have(
        Exists(d, d > 0, ForAll(y, abs(p - y) < d, abs(f[p] - f[y]) < eps / 2)), by=[]
    )
    l.clear(hf)
    d1 = l.obtain(witness_f)
    witness_g = l.have(
        Exists(d, d > 0, ForAll(y, abs(p - y) < d, abs(g[p] - g[y]) < eps / 2)), by=[]
    )
    l.clear(hg)
    d2 = l.obtain(witness_g)
    l.exists(min(d1, d2))
    l.auto(by=[abs.defn, min.defn])


@Theorem(ForAll([f, g, p], cont_at(f, p), cont_at(g, p), cont_at(f * g, p)))
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
    hf = l.specialize(hf, eta)
    hg = l.specialize(hg, eta)
    d, y = Reals("delta y")
    witness_f = l.have(
        Exists(d, d > 0, ForAll(y, abs(p - y) < d, abs(f[p] - f[y]) < eta)), by=[]
    )
    l.clear(hf)
    d1 = l.obtain(witness_f)
    witness_g = l.have(
        Exists(d, d > 0, ForAll(y, abs(p - y) < d, abs(g[p] - g[y]) < eta)), by=[]
    )
    l.clear(hg)
    d2 = l.obtain(witness_g)
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
    ForAll([f, g], is_cont(f), is_cont(g), is_cont(f + g)),
    by=[is_cont.defn, cont_at_add],
)

is_cont_mul = prove(
    ForAll([f, g], is_cont(f), is_cont(g), is_cont(f * g)),
    by=[is_cont.defn, cont_at_mul],
)


# Updating the value at p turns a punctured limit into continuity at p.
@Theorem(ForAll([f, p, L], has_lim_at(f, p, L), cont_at(Store(f, p, L), p)))
def cont_at_update_of_has_lim_at(l):
    f, p, L = l.fixes()
    l.unfold(has_lim_at, cont_at)
    limit = l.intros()
    eps = l.fix()
    l.intros()
    limit = l.specialize(limit, eps)
    d, x = Reals("delta x")
    witness = l.have(
        Exists(
            d,
            d > 0,
            ForAll(x, RealVal(0) < abs(x - p), abs(x - p) < d, abs(f[x] - L) < eps),
        ),
        by=[],
    )
    l.clear(limit)
    delta = l.obtain(witness)
    l.exists(delta)
    l.auto(by=[abs.defn])


@Theorem(ForAll([f, p, L], cont_at(Store(f, p, L), p), has_lim_at(f, p, L)))
def has_lim_at_of_cont_at_update(l):
    f, p, L = l.fixes()
    l.unfold(cont_at, has_lim_at)
    continuity = l.intros()
    eps = l.fix()
    l.intros()
    continuity = l.specialize(continuity, eps)
    d, y = Reals("delta y")
    updated = Store(f, p, L)
    witness = l.have(
        Exists(d, d > 0, ForAll(y, abs(p - y) < d, abs(updated[p] - updated[y]) < eps)),
        by=[],
    )
    l.clear(continuity)
    delta = l.obtain(witness)
    l.split(at=-1)  # Separate positivity from the universal error bound.
    tail = l.top_goal().ctx[-1]
    l.exists(delta)
    l.split()
    l.assumption()

    # Instantiate continuity at the point in the punctured neighborhood.
    x = l.fix()
    l.intros()
    l.intros()
    l.specialize(tail, x)
    l.auto(
        by=[
            abs.defn(x - p),
            abs.defn(p - x),
            abs.defn(L - f[x]),
            abs.defn(f[x] - L),
        ]
    )


@Theorem(
    ForAll(
        [f, g, p, L, M],
        has_lim_at(f, p, L),
        has_lim_at(g, p, M),
        has_lim_at(f + g, p, L + M),
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
        has_lim_at(f, p, L),
        has_lim_at(g, p, M),
        has_lim_at(f * g, p, L * M),
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
continuous_at_const = exact(
    ForAll([a, p], cont_at(Lambda(x, a), p)),
    cont_at_of_is_cont(Lambda(x, a), p, continuous_const(a)).forall([a, p]),
)
continuous_at_id = exact(
    ForAll(p, cont_at(Lambda(x, x), p)),
    cont_at_of_is_cont(Lambda(x, x), p, continuous_id).forall([p]),
)
continuous_at_add_const = exact(
    ForAll([a, p], cont_at(Lambda(x, x + a), p)),
    cont_at_of_is_cont(Lambda(x, x + a), p, continuous_add_const(a)).forall([a, p]),
)
continuous_at_sq = exact(
    ForAll(p, cont_at(Lambda(x, x * x), p)),
    cont_at_of_is_cont(Lambda(x, x * x), p, continuous_sq).forall([p]),
)
continuous_at_cube = exact(
    ForAll(p, cont_at(Lambda(x, x * x * x), p)),
    cont_at_of_is_cont(Lambda(x, x * x * x), p, continuous_cube).forall([p]),
)
continuous_at_abs = exact(
    ForAll(p, cont_at(Lambda(x, abs(x)), p)),
    cont_at_of_is_cont(Lambda(x, abs(x)), p, continuous_abs).forall([p]),
)

# A continuous function tends to its value at the point.
has_lim_at_const = exact(
    ForAll([a, p], has_lim_at(Lambda(x, a), p, Lambda(x, a)[p])),
    has_lim_at_of_cont_at(Lambda(x, a), p, continuous_at_const(a, p)).forall([a, p]),
)
has_lim_at_id = exact(
    ForAll(p, has_lim_at(Lambda(x, x), p, Lambda(x, x)[p])),
    has_lim_at_of_cont_at(Lambda(x, x), p, continuous_at_id(p)).forall([p]),
)
has_lim_at_add_const = exact(
    ForAll([a, p], has_lim_at(Lambda(x, x + a), p, Lambda(x, x + a)[p])),
    has_lim_at_of_cont_at(Lambda(x, x + a), p, continuous_at_add_const(a, p)).forall(
        [a, p]
    ),
)
has_lim_at_sq = exact(
    ForAll(p, has_lim_at(Lambda(x, x * x), p, Lambda(x, x * x)[p])),
    has_lim_at_of_cont_at(Lambda(x, x * x), p, continuous_at_sq(p)).forall([p]),
)
has_lim_at_cube = exact(
    ForAll(p, has_lim_at(Lambda(x, x * x * x), p, Lambda(x, x * x * x)[p])),
    has_lim_at_of_cont_at(Lambda(x, x * x * x), p, continuous_at_cube(p)).forall([p]),
)
has_lim_at_abs = exact(
    ForAll(p, has_lim_at(Lambda(x, abs(x)), p, Lambda(x, abs(x))[p])),
    has_lim_at_of_cont_at(Lambda(x, abs(x)), p, continuous_at_abs(p)).forall([p]),
)
