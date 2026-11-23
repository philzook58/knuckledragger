"""Gauge (Henstock-Kurzweil) integral and the fundamental theorem of calculus.

A tagged partition of `[a, b]` is a length `n` with point and tag sequences

    a = xs[0] <= ts[0] <= xs[1] <= ... <= ts[n - 1] <= xs[n] = b.

It is fine for a positive gauge `D` when each cell `[xs[i], xs[i + 1]]` lies in
the open ball of radius `D[ts[i]]` around its tag. Gauges replace the single mesh
width of the Riemann integral, which makes every derivative integrable.
"""

import kdrag as kd
import kdrag.smt as smt
import kdrag.theories.int as int_
from kdrag import FreshVar, FreshVars, Theorem, define, prove
from kdrag.smt import (
    And,
    ArraySort,
    BoolSort,
    Const,
    Consts,
    Exists,
    ForAll,
    Implies,
    Ints,
    IntSort,
    IntVal,
    K,
    Lambda,
    Reals,
    RealVal,
    Store,
)
from kdrag.theories.real import R, RFun, RSeq, abs, abs_mul, abs_neg, min
from kdrag.contrib.analysis.rseq import abs_finsum_le, finsum_diff, finsum_sub
from kdrag.theories.real.rseq import (
    diff,
    finsum,
    finsum_smul,
    smul,
    sub,
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

# A pointwise choice of radii is a gauge function.
P = Const("P", ArraySort(R, R, BoolSort()))
_P, _x = FreshVar("P", P.sort()), FreshVar("x", R)
assert isinstance(_P, smt.ArrayRef)
(_choice,), _choice_spec = kd.kernel.obtain(Exists(y, _P[_x, y]))


@Theorem(ForAll(P, ForAll(x, Exists(y, P[x, y])), Exists(D, ForAll(x, P[x, D[x]]))))
def axiom_of_choice(l):
    P = l.fix()
    l.intro()
    l.exists(Lambda(_x, smt.substitute(_choice, (_P, P))))
    z = l.fix()
    l.auto(by=[_choice_spec.forall([_P, _x])(P, z)])


# mathlib's `HasDerivAt F k x`: F y = F x + k * (y - x) + o(y - x).
has_deriv_at = define(
    "has_deriv_at",
    [F, k, x],
    ForAll(
        eps,
        eps > 0,
        Exists(
            delta,
            delta > 0,
            ForAll(
                y,
                abs(y - x) < delta,
                abs(F[y] - F[x] - k * (y - x)) <= eps * abs(y - x),
            ),
        ),
    ),
)


def straddles(F, k, t, delta, eps) -> smt.BoolRef:
    """Every interval around `t` inside the `delta` ball is within `eps` of slope `k`."""
    return ForAll(
        [u, v],
        t - delta < u,
        u <= t,
        t <= v,
        v < t + delta,
        abs(F[v] - F[u] - k * (v - u)) <= eps * (v - u),
    )


@Theorem(
    ForAll(
        [F, k, t, eps],
        has_deriv_at(F, k, t),
        eps > 0,
        Exists(delta, delta > 0, straddles(F, k, t, delta, eps)),
    )
)
def straddle_of_has_deriv_at(l):
    F, k, t, eps = l.fixes()
    l.unfold(has_deriv_at)
    h = l.intro()
    l.intro()
    h = l.specialize(h, eps / 2)
    witness = l.have(
        Exists(
            delta,
            delta > 0,
            ForAll(
                y,
                abs(y - t) < delta,
                abs(F[y] - F[t] - k * (y - t)) <= eps / 2 * abs(y - t),
            ),
        ),
        by=[],
    )
    l.clear(h)
    r = l.obtain(witness)
    l.split(at=-1)
    near = l.top_goal().ctx[-1]
    l.exists(r)
    l.split()
    l.assumption()
    u, v = l.fixes()
    l.intros()
    # Split [u, v] at t and compare each half with the tangent line at t.
    l.have(abs(F[u] - F[t] - k * (u - t)) <= eps / 2 * abs(u - t), by=[abs.defn(u - t)])
    l.have(abs(F[v] - F[t] - k * (v - t)) <= eps / 2 * abs(v - t), by=[abs.defn(v - t)])
    l.clear(near)
    l.auto(
        by=[
            abs.defn(u - t),
            abs.defn(v - t),
            abs.defn(F[v] - F[u] - k * (v - u)),
            abs.defn(F[u] - F[t] - k * (u - t)),
            abs.defn(F[v] - F[t] - k * (v - t)),
        ]
    )


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
        [F, f, a, b],
        ForAll(x, a <= x, x <= b, has_deriv_at(F, f[x], x)),
        has_integral(f, a, b, F[b] - F[a]),
    )
)
def has_integral_sub_of_has_deriv_at(l):
    """Fundamental theorem of calculus: a derivative integrates to the net change."""
    F, f, a, b = l.fixes()
    hderiv = l.intro()
    l.unfold(has_integral)
    eps = l.fix()
    l.intro()
    # Spread the error budget over the length of [a, b].
    heta = l.have(Exists(y, y > 0, y * (abs(b - a) + 1) == eps))
    l.exists(eps / (abs(b - a) + 1))
    l.auto(by=[abs.defn(b - a)])
    eta = l.obtain(heta)

    # Choose a straddle radius at every point, using radius 1 outside [a, b].
    Q = Lambda(
        [t, delta],
        And(delta > 0, Implies(And(a <= t, t <= b), straddles(F, f[t], t, delta, eta))),
    )
    # Match the binder names of axiom_of_choice so its premise is syntactic.
    l.have(ForAll(x, Exists(y, Q[x, y])))
    s = l.fix()
    l.cases(And(a <= s, s <= b))
    w = l.have(
        Exists(delta, delta > 0, straddles(F, f[s], s, delta, eta)),
        by=[straddle_of_has_deriv_at(F, f[s], s, eta)],
    )
    l.clear(hderiv)
    r = l.obtain(w)
    l.exists(r)
    l.beta()
    l.auto()
    l.exists(RealVal(1))
    l.beta()
    l.auto()
    hchoice = l.top_goal().ctx[-1]
    l.have(Exists(D, ForAll(x, Q[x, D[x]])), by=[axiom_of_choice(Q)])
    gauge = l.obtain(-1)
    hgauge = l.top_goal().ctx[-1]
    l.clear(hchoice)
    l.clear(hderiv)
    l.exists(gauge)
    l.split()
    l.auto()
    xs, ts, n = l.fixes()
    l.intros()
    # Keep the partition hypotheses folded and unfold them only where needed.
    tagged = is_tagged_partition.defn(xs, ts, n, a, b)
    fine = is_fine.defn(gauge, xs, ts, n)

    # The error telescopes into a sum of per-cell errors.
    terms = Lambda(i, f[ts[i]] * (xs[i + 1] - xs[i]))
    Fxs = Lambda(i, F[xs[i]])
    err = terms - diff(Fxs)
    l.have(
        riemann_sum(f, xs, ts, n) - (F[b] - F[a]) == finsum(err, n),
        by=[
            riemann_sum.defn(f, xs, ts, n),
            finsum_sub(terms, diff(Fxs), n),
            finsum_diff(Fxs, n),
            tagged,
        ],
    )
    # Each cell straddles its tag, so its error is at most eta times its length.
    bound = smul(eta, diff(xs))
    hbound = l.have(ForAll(i, 0 <= i, i < n, abs(err[i]) <= bound[i]))
    j = l.fix()
    l.intros()
    tj, x0, x1 = ts[j], xs[j], xs[j + 1]
    l.have(
        And(
            a <= tj,
            tj <= b,
            x0 <= tj,
            tj <= x1,
            tj - gauge[tj] < x0,
            x1 < tj + gauge[tj],
        ),
        by=[mem_icc_of_is_tagged_partition(xs, ts, n, a, b), tagged, fine],
    )
    hstraddle = l.have(straddles(F, f[tj], tj, gauge[tj], eta), by=[])
    l.have(abs(F[x1] - F[x0] - f[tj] * (x1 - x0)) <= eta * (x1 - x0), by=[])
    l.clear(hstraddle)
    l.clear(hgauge)
    l.have(
        err[j] == -(F[x1] - F[x0] - f[tj] * (x1 - x0)),
        by=[sub.defn(terms, diff(Fxs)), diff.defn(Fxs)],
    )
    l.have(bound[j] == eta * (x1 - x0), by=[smul.defn(eta, diff(xs)), diff.defn(xs)])
    l.auto(by=[abs_neg(F[x1] - F[x0] - f[tj] * (x1 - x0))])

    # Sum the cell bounds: eta * (b - a) <= eta * |b - a| < eta * (|b - a| + 1) = eps.
    l.have(
        abs(finsum(err, n)) <= finsum(bound, n),
        by=[abs_finsum_le(err, bound, n), tagged],
    )
    l.clear(hgauge)
    l.clear(hbound)
    l.have(
        finsum(bound, n) == eta * (b - a),
        by=[finsum_smul(diff(xs), eta, n), finsum_diff(xs, n), tagged],
    )
    l.have(eta * (b - a) <= eta * abs(b - a), by=[abs.defn(b - a)])
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
    c = l.obtain(hlub)
    l.have(
        And(a <= c, c <= b),
        by=[is_lub.defn(S, c), is_ub.defn(S, c), le_of_is_lub_of_is_ub(S, c, b)],
    )
    l.have(Exists(x, S[x], c - D[c] < x))
    l.auto(by=[le_of_is_lub_of_is_ub(S, c, c - D[c]), is_ub.defn(S, c - D[c])])
    x0 = l.obtain(-1)
    l.have(x0 <= c, by=[is_lub.defn(S, c), is_ub.defn(S, c)])
    hpart = l.have(
        Exists(
            [xs, ts, n], is_tagged_partition(xs, ts, n, a, x0), is_fine(D, xs, ts, n)
        ),
        by=[],
    )
    xs0, ts0, n0 = l.obtain(hpart)
    htag = l.top_goal().ctx[-1]

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
    D1 = l.obtain(hI)
    D2 = l.obtain(hJ)
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
    xs0, ts0, n0 = l.obtain(hpart)
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


@Theorem(
    ForAll(
        [F, f, a, b],
        a <= b,
        ForAll(x, a <= x, x <= b, has_deriv_at(F, f[x], x)),
        integral(f, a, b) == F[b] - F[a],
    )
)
def integral_eq_sub_of_has_deriv_at(l):
    """Fundamental theorem of calculus for the `integral` function."""
    F, f, a, b = l.fixes()
    l.intros()
    l.have(
        has_integral(f, a, b, F[b] - F[a]),
        by=[has_integral_sub_of_has_deriv_at(F, f, a, b)],
    )
    l.auto(by=[integral_eq_of_has_integral(f, a, b, F[b] - F[a])])


@Theorem(ForAll(x, has_deriv_at(Lambda(t, t * t), 2 * x, x)))
def has_deriv_at_sq(l):
    x = l.fix()
    l.unfold(has_deriv_at)
    eps = l.fix()
    l.intro()
    # The error is (y - x)^2, so delta = eps works.
    l.exists(eps)
    l.split()
    l.auto()
    y = l.fix()
    l.intro()
    l.beta()
    l.have(y * y - x * x - 2 * x * (y - x) == (y - x) * (y - x), by=[])
    l.auto(by=[abs.defn(y - x), abs.defn((y - x) * (y - x)), abs_mul(y - x, y - x)])


@Theorem(integral(Lambda(t, 2 * t), 0, 1) == 1)
def integral_two_mul_id(l):
    sq, two_mul = Lambda(t, t * t), Lambda(t, 2 * t)
    # Write 0 <= x with RealVal so it matches the instantiated hypothesis.
    l.have(ForAll(x, RealVal(0) <= x, x <= 1, has_deriv_at(sq, two_mul[x], x)))
    z = l.fix()
    l.intros()
    l.beta()
    l.auto(by=[has_deriv_at_sq(z)])
    l.auto(by=[integral_eq_sub_of_has_deriv_at(sq, two_mul, 0, 1)])
