"""Pointwise real limits, congruence, and continuity of compositions."""

from kdrag import Theorem, define
from kdrag.smt import (
    And,
    Const,
    Consts,
    Exists,
    FullSet,
    If,
    IntVal,
    Lambda,
    Not,
    ForAll,
    RealVal,
    Reals,
    Store,
)
from kdrag.theories.real import (
    A,
    R,
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
    icc,
    min,
    sqr,
    sqr_sqrt,
    sqrt,
    sqrt_pos,
    sqrt_sqr,
    sqrt_zero,
)
from kdrag.theories.real.cont import (
    cont_at_update_of_has_lim_at,
    has_lim_at_of_cont_at_update,
)
from kdrag.theories.real.rseq import a as seq_a, has_lim, n

f, g = Consts("f g", RFun)
B = Const("B", A.sort())
x, y, p, L, M, c = Reals("x y p L M c")


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

cont_within_at = define(
    "analysis.cont_within_at",
    [f, A, p],
    ForAll(
        eps,
        eps > 0,
        Exists(
            delta,
            delta > 0,
            ForAll(x, A[x], abs(p - x) < delta, abs(f[p] - f[x]) < eps),
        ),
    ),
)
cont_on = define("analysis.cont_on", [f, A], ForAll(p, A[p], cont_within_at(f, A, p)))


@Theorem(ForAll([f, A, B, p], cont_within_at(f, A, p), B <= A, cont_within_at(f, B, p)))
def cont_within_at_mono(l):
    """Continuity within a set restricts to its subsets at the same point."""
    f, A, B, p = l.fixes()
    l.unfold(cont_within_at)
    continuous, _ = l.intros()
    eps = l.fix()
    positive = l.intro()
    radius, witness = l.obtain(l.specialize(continuous, eps, positive))
    _, images_close = l.andE(witness)
    l.exists(radius)
    l.split()
    l.auto()
    x = l.fix()
    l.intros()
    l.specialize(images_close, x)
    l.auto()


@Theorem(ForAll([f, A, B], cont_on(f, A), B <= A, cont_on(f, B)))
def cont_on_mono(l):
    """Restrict a continuous function to a subset of its domain."""
    f, A, B = l.fixes()
    l.unfold(cont_on)
    continuous, _ = l.intros()
    p = l.fix()
    l.intro()
    l.specialize(continuous, p)
    l.auto(by=[cont_within_at_mono(f, A, B, p)])


@Theorem(ForAll([f, A, p], cont_at(f, p), cont_within_at(f, A, p)))
def cont_within_at_of_cont_at(l):
    f, A, p = l.fixes()
    l.unfold(cont_at, cont_within_at)
    continuous = l.intro()
    eps = l.fix()
    positive = l.intro()
    delta, witness = l.obtain(l.specialize(continuous, eps, positive))
    _, images_close = l.andE(witness)
    l.exists(delta)
    l.split()
    l.auto()
    x = l.fix()
    l.intros()
    l.specialize(images_close, x)
    l.auto()


@Theorem(
    ForAll(
        [f, g, A, p],
        cont_within_at(f, A, p),
        cont_within_at(g, A, p),
        cont_within_at(Lambda(x, f[x] - g[x]), A, p),
    )
)
def cont_within_at_sub(l):
    """The difference of two functions continuous within a set is continuous there."""
    f, g, A, p = l.fixes()
    l.unfold(cont_within_at)
    hf, hg = l.intros()
    eps = l.fix()
    l.intro()
    half = l.have(eps / 2 > 0, by=[])
    r1, near_f = l.obtain(l.specialize(hf, eps / 2, half))
    r2, near_g = l.obtain(l.specialize(hg, eps / 2, half))
    _, near_f = l.andE(near_f)
    _, near_g = l.andE(near_g)

    # Use a radius that keeps both image differences below half epsilon.
    l.exists(min(r1, r2))
    l.split()
    l.auto(by=[min.defn(r1, r2)])
    q = l.fix()
    member, _ = l.intros()
    l.specialize(near_f, q, member)
    l.specialize(near_g, q, member)
    df, dg = f[p] - f[q], g[p] - g[q]
    l.beta()
    l.auto(by=[min.defn(r1, r2), abs.defn(df), abs.defn(dg), abs.defn(df - dg)])


@Theorem(
    ForAll(
        [seq_a, f, A, p],
        has_lim(seq_a, p),
        ForAll(n, n >= 0, A[seq_a[n]]),
        cont_within_at(f, A, p),
        has_lim(Lambda(n, f[seq_a[n]]), f[p]),
    )
)
def has_lim_comp_of_cont_within_at(l):
    """Continuity within a set preserves limits of sequences in that set."""
    a, f, A, p = l.fixes()
    l.unfold(has_lim, cont_within_at)
    tends, in_set, continuous = l.intros()
    eps = l.fix()
    positive = l.intro()
    delta, witness = l.obtain(l.specialize(continuous, eps, positive))
    delta_positive, images_close = l.andE(witness)
    N, terms_close = l.obtain(l.specialize(tends, delta, delta_positive))
    l.exists(If(N < 0, IntVal(0), N))
    j = l.fix()
    l.intro()
    l.specialize(in_set, j)
    l.specialize(terms_close, j)
    l.specialize(images_close, a[j])
    l.auto(by=[abs_neg(a[j] - p), abs_neg(f[p] - f[a[j]])])


@Theorem(
    ForAll(
        [seq_a, f, p],
        has_lim(seq_a, p),
        cont_at(f, p),
        has_lim(Lambda(n, f[seq_a[n]]), f[p]),
    )
)
def has_lim_comp_of_cont_at(l):
    """A function continuous at the limit preserves sequence convergence."""
    a, f, p = l.fixes()
    l.intros()
    all_reals = FullSet(R)
    l.have(ForAll(n, n >= 0, all_reals[a[n]]), by=[])
    l.auto(
        by=[
            cont_within_at_of_cont_at(f, all_reals, p),
            has_lim_comp_of_cont_within_at(a, f, all_reals, p),
        ]
    )


_has_uniform_radius = define(
    "analysis.has_uniform_radius",
    [f, A, eps],
    Exists(
        delta,
        delta > 0,
        ForAll([x, y], A[x], A[y], abs(x - y) < delta, abs(f[x] - f[y]) < eps),
    ),
)
uniform_cont_on = define(
    "analysis.uniform_cont_on",
    [f, A],
    ForAll(eps, eps > 0, _has_uniform_radius(f, A, eps)),
)


lipschitz_on = define(
    "analysis.lipschitz_on",
    [f, A],
    Exists(
        M,
        M > 0,
        ForAll([x, y], A[x], A[y], abs(f[x] - f[y]) <= M * abs(x - y)),
    ),
)


@Theorem(ForAll([f, A], lipschitz_on(f, A), uniform_cont_on(f, A)))
def uniform_cont_on_of_lipschitz_on(l):
    """Abbott 4.4.9(a)."""
    f, A = l.fixes()
    l.unfold(lipschitz_on, uniform_cont_on)
    K, bound = l.obtain(l.intro())
    _, slopes = l.andE(bound)
    eps = l.fix()
    l.intro()
    l.unfold(_has_uniform_radius)
    # Scale the requested output tolerance by the slope bound.
    radius = eps / K
    l.exists(radius)
    l.split()
    l.auto()
    x, y = l.fixes()
    l.intros()
    l.specialize(slopes, x, y)
    l.auto()


_sqrt_fun = Lambda(x, sqrt(x))
_unit_interval = icc(0, 1)


@Theorem(uniform_cont_on(_sqrt_fun, _unit_interval))
def uniform_cont_on_sqrt_unit_interval(l):
    l.unfold(uniform_cont_on)
    eps = l.fix()
    l.intro()
    l.unfold(_has_uniform_radius)
    l.exists(eps * eps)
    l.split()
    l.auto()
    x, y = l.fixes()
    l.intros()
    l.have(And(x >= 0, y >= 0), by=[icc.defn(0, 1)])
    a, b = sqrt(x), sqrt(y)
    # The squared output difference is bounded by the input difference.
    d = a - b
    l.have(
        d * d <= abs(x - y),
        by=[
            sqrt_pos(x),
            sqrt_pos(y),
            sqr_sqrt(x),
            sqr_sqrt(y),
            sqr.defn(a),
            sqr.defn(b),
            abs.defn(x - y),
        ],
    )
    l.auto(by=[abs.defn(d)])


@Theorem(Not(lipschitz_on(_sqrt_fun, _unit_interval)))
def not_lipschitz_on_sqrt_unit_interval(l):
    """The square root gives the counterexample in Abbott 4.4.9(b)."""
    l.unfold(lipschitz_on)
    K, bound = l.obtain(l.intro())
    _, slopes = l.andE(bound)
    # At x = t² and y = 0 the proposed bound would give 1 ≤ Kt.
    t = RealVal(1) / (K + 1)
    l.have(And(t > 0, t <= 1, K * t < 1), by=[])
    x = sqr(t)
    zero = RealVal(0)
    l.specialize(slopes, x, zero)
    l.auto(
        by=[
            icc.defn(0, 1),
            sqrt_sqr(t),
            sqrt_zero,
            sqr.defn(t),
            abs.defn(x - zero),
            abs.defn(sqrt(x) - sqrt(zero)),
        ],
    )


@Theorem(
    ForAll(
        [f, A, p, eps],
        cont_within_at(f, A, p),
        eps > 0,
        Exists(
            delta,
            delta > 0,
            ForAll(
                [x, y],
                A[x],
                A[y],
                abs(x - p) < delta,
                abs(x - y) < delta,
                abs(f[x] - f[y]) < eps,
            ),
        ),
    )
)
def exists_pair_radius_of_cont_within_at(l):
    """Two close points near p have close images."""
    f, A, p, eps = l.fixes()
    l.unfold(cont_within_at)
    continuous, _ = l.intros()
    positive = l.have(eps / 2 > 0, by=[])
    radius, witness = l.obtain(l.specialize(continuous, eps / 2, positive))
    _, close_images = l.andE(witness)
    l.exists(radius / 2)
    l.split()
    l.auto()
    x, y = l.fixes()
    l.intros()
    l.specialize(close_images, x, keep=True)
    l.specialize(close_images, y)
    l.auto(
        by=[
            abs_neg(x - p),
            abs_neg(x - y),
            abs_triangle(p, y, x),
            abs_neg(f[p] - f[x]),
            abs_triangle(f[x], f[y], f[p]),
        ]
    )


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
