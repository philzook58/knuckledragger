"""Gauge (Henstock-Kurzweil) integral, partitions, existence, and uniqueness.

A tagged partition of `[a, b]` is a length `n` with point and tag sequences

    a = xs[0] <= ts[0] <= xs[1] <= ... <= ts[n - 1] <= xs[n] = b.

It is fine for a positive gauge `D` when each cell `[xs[i], xs[i + 1]]` lies in
the open ball of radius `D[ts[i]]` around its tag. Gauges replace the single mesh
width of the Riemann integral, which makes every derivative integrable.
"""

import kdrag as kd
import kdrag.theories.int as int_
from kdrag import FreshVars, Theorem, define, prove
from kdrag.smt import (
    And,
    Consts,
    Exists,
    ForAll,
    Ints,
    IntSort,
    IntVal,
    K,
    Lambda,
    Reals,
    Store,
)
from kdrag.theories.real import R, RFun, RSeq, abs, min
from kdrag.theories.real.rseq import (
    finsum,
)
from kdrag.theories.real.rset import (
    bdd_above,
    exists_is_lub_of_bdd_above,
    is_lub,
    is_ub,
    le_of_is_lub_of_is_ub,
)

f, F, D, E = Consts("f F D E", RFun)
xs, ts = Consts("xs ts", RSeq)
a, b, k, t, u, v, x, y, eps, delta, I, J = Reals("a b k t u v x y eps delta I J")
i, n = Ints("i n")

is_tagged_partition = define(
    "is_tagged_partition",
    [xs, ts, n, a, b],
    And(
        n >= 0,
        xs[0] == a,
        xs[n] == b,
        ForAll(i, 0 <= i, i < n, And(xs[i] <= ts[i], ts[i] <= xs[i + 1])),
    ),
)
is_fine = define(
    "is_fine",
    [D, xs, ts, n],
    ForAll(
        i, 0 <= i, i < n, And(ts[i] - D[ts[i]] < xs[i], xs[i + 1] < ts[i] + D[ts[i]])
    ),
)
riemann_sum = define(
    "riemann_sum",
    [f, xs, ts, n],
    finsum(Lambda(i, f[ts[i]] * (xs[i + 1] - xs[i])), n),
)
has_integral = define(
    "has_integral",
    [f, a, b, I],
    ForAll(
        eps,
        eps > 0,
        Exists(
            D,
            ForAll(x, D[x] > 0),
            ForAll(
                [xs, ts, n],
                is_tagged_partition(xs, ts, n, a, b),
                is_fine(D, xs, ts, n),
                abs(riemann_sum(f, xs, ts, n) - I) < eps,
            ),
        ),
    ),
)


@Theorem(
    ForAll(
        [xs, n],
        ForAll(i, 0 <= i, i < n, xs[i] <= xs[i + 1]),
        n >= 0,
        ForAll(i, 0 <= i, i <= n, And(xs[0] <= xs[i], xs[i] <= xs[n])),
    )
)
def le_of_monotone_steps(l):
    xs, n = l.fixes()
    # Extend the bounds one point at a time.
    l.induct(n, using=int_.induct_nat)
    l.auto()
    n = l.fix()
    l.intros()
    l.have(xs[n] <= xs[n + 1], by=[])
    l.auto()


@Theorem(
    ForAll(
        [xs, ts, n, a, b],
        is_tagged_partition(xs, ts, n, a, b),
        ForAll(i, 0 <= i, i < n, And(a <= ts[i], ts[i] <= b)),
    )
)
def mem_icc_of_is_tagged_partition(l):
    xs, _ts, n, a, b = l.fixes()
    l.unfold(is_tagged_partition)
    l.intro()
    # Points increase from a to b, and each tag sits between two points.
    l.have(
        ForAll(i, 0 <= i, i <= n, And(a <= xs[i], xs[i] <= b)),
        by=[le_of_monotone_steps(xs, n)],
    )
    l.auto()


@Theorem(
    ForAll(
        [D, a, b],
        ForAll(x, D[x] > 0),
        a <= b,
        Exists(
            [xs, ts, n], is_tagged_partition(xs, ts, n, a, b), is_fine(D, xs, ts, n)
        ),
    )
)
def exists_tagged_partition_is_fine(l):
    """Cousin's lemma: every positive gauge has a fine tagged partition."""
    D, a, b = l.fixes()
    l.intros()
    # S is the set of right endpoints reachable by a fine partition from a.
    S = Lambda(
        x,
        And(
            a <= x,
            x <= b,
            Exists(
                [xs, ts, n], is_tagged_partition(xs, ts, n, a, x), is_fine(D, xs, ts, n)
            ),
        ),
    )
    # The trivial partition reaches a itself.
    l.have(S[a])
    l.beta()
    l.split()
    l.auto()
    l.auto()
    l.exists(K(IntSort(), a), K(IntSort(), a), IntVal(0))
    l.auto(by=[is_tagged_partition.defn, is_fine.defn])

    # Take the supremum c of S; some reachable x lies within D[c] below it.
    l.have(is_ub(S, b), by=[is_ub.defn(S, b)])
    hlub = l.have(
        Exists(u, is_lub(S, u)), by=[exists_is_lub_of_bdd_above(S), bdd_above.defn(S)]
    )
    c, _ = l.obtain(hlub)
    l.have(
        And(a <= c, c <= b),
        by=[is_lub.defn(S, c), is_ub.defn(S, c), le_of_is_lub_of_is_ub(S, c, b)],
    )
    l.have(Exists(x, S[x], c - D[c] < x))
    l.auto(by=[le_of_is_lub_of_is_ub(S, c, c - D[c]), is_ub.defn(S, c - D[c])])
    x0, _ = l.obtain(-1)
    l.have(x0 <= c, by=[is_lub.defn(S, c), is_ub.defn(S, c)])
    hpart = l.have(
        Exists(
            [xs, ts, n], is_tagged_partition(xs, ts, n, a, x0), is_fine(D, xs, ts, n)
        ),
        by=[],
    )
    (xs0, ts0, n0), htag = l.obtain(hpart)

    # Append the cell [x0, c1] tagged by c; it is fine and reaches c1 = min(b, c + D[c] / 2).
    c1 = min(b, c + D[c] / 2)
    xs1, ts1 = Store(xs0, n0 + 1, c1), Store(ts0, n0, c)
    l.have(And(c <= c1, c1 < c + D[c], c1 <= b), by=[min.defn(b, c + D[c] / 2)])
    l.unfold(is_tagged_partition, is_fine, at=htag)
    l.have(
        is_tagged_partition(xs1, ts1, n0 + 1, a, c1),
        by=[is_tagged_partition.defn(xs1, ts1, n0 + 1, a, c1)],
    )
    l.have(is_fine(D, xs1, ts1, n0 + 1), by=[is_fine.defn(D, xs1, ts1, n0 + 1)])
    # So c1 is reachable, hence c1 <= c, which forces c = b = c1.
    l.have(S[c1])
    l.beta()
    l.split()
    l.auto()
    l.auto()
    l.exists(xs1, ts1, n0 + 1)
    l.auto()
    l.have(c1 <= c, by=[is_lub.defn(S, c), is_ub.defn(S, c)])
    l.have(c1 == b, by=[min.defn(b, c + D[c] / 2)])
    l.exists(xs1, ts1, n0 + 1)
    l.auto()


@Theorem(
    ForAll(
        [D, E, xs, ts, n],
        ForAll(x, D[x] <= E[x]),
        is_fine(D, xs, ts, n),
        is_fine(E, xs, ts, n),
    )
)
def is_fine_mono(l):
    D, E, _xs, ts, _n = l.fixes()
    l.unfold(is_fine)
    l.intros()
    j = l.fix()
    l.intros()
    l.have(E[ts[j]] >= D[ts[j]], by=[])
    l.auto()


@Theorem(
    ForAll(
        [f, a, b, I, J],
        a <= b,
        has_integral(f, a, b, I),
        has_integral(f, a, b, J),
        I == J,
    )
)
def has_integral_unique(l):
    f, a, b, I, J = l.fixes()
    _, hI, hJ = l.intros()
    # Two different values would both be within |I - J| / 2 of one Riemann sum.
    l.unfold(has_integral, at=hI)
    l.unfold(has_integral, at=hJ)
    hI, hJ = l.top_goal().ctx[-2:]
    l.contra()
    eps = abs(I - J) / 2
    hpos = l.have(eps > 0, by=[abs.defn(I - J)])
    hI = l.specialize(hI, eps, hpos)
    hJ = l.specialize(hJ, eps, hpos)
    D1, _ = l.obtain(hI)
    D2, _ = l.obtain(hJ)
    # Refine both gauges at once and take a partition fine for both.
    G = Lambda(x, min(D1[x], D2[x]))
    l.have(ForAll(x, G[x] > 0), by=[min.defn])
    l.have(ForAll(x, G[x] <= D1[x]), by=[min.defn])
    l.have(ForAll(x, G[x] <= D2[x]), by=[min.defn])
    hpart = l.have(
        Exists(
            [xs, ts, n], is_tagged_partition(xs, ts, n, a, b), is_fine(G, xs, ts, n)
        ),
        by=[exists_tagged_partition_is_fine(G, a, b)],
    )
    (xs0, ts0, n0), _ = l.obtain(hpart)
    l.have(is_fine(D1, xs0, ts0, n0), by=[is_fine_mono(G, D1, xs0, ts0, n0)])
    l.have(is_fine(D2, xs0, ts0, n0), by=[is_fine_mono(G, D2, xs0, ts0, n0)])
    sm = riemann_sum(f, xs0, ts0, n0)
    l.have(And(abs(sm - I) < eps, abs(sm - J) < eps), by=[])
    l.auto(by=[abs.defn(sm - I), abs.defn(sm - J), abs.defn(I - J)])


is_integrable = define("is_integrable", [f, a, b], Exists(I, has_integral(f, a, b, I)))

# Choose the integral where it exists; uniqueness makes the choice canonical.
(_f,), (_a, _b) = FreshVars("f", RFun), FreshVars("a b", R)
(_integral,), _integral_spec = kd.kernel.obtain(Exists(I, has_integral(_f, _a, _b, I)))
integral = define("integral", [_f, _a, _b], _integral)

has_integral_integral = prove(
    ForAll([f, a, b], is_integrable(f, a, b), has_integral(f, a, b, integral(f, a, b))),
    by=[is_integrable.defn, integral.defn, _integral_spec.forall([_f, _a, _b])],
)


@Theorem(ForAll([f, a, b, I], a <= b, has_integral(f, a, b, I), integral(f, a, b) == I))
def integral_eq_of_has_integral(l):
    f, a, b, I = l.fixes()
    l.intros()
    l.have(is_integrable(f, a, b), by=[is_integrable.defn(f, a, b)])
    l.have(
        has_integral(f, a, b, integral(f, a, b)), by=[has_integral_integral(f, a, b)]
    )
    l.auto(by=[has_integral_unique(f, a, b, integral(f, a, b), I)])
