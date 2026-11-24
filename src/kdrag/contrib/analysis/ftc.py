"""Fundamental theorem of calculus and its integral-evaluation example."""

from kdrag import Theorem
from kdrag.smt import And, Consts, Exists, ForAll, Implies, Ints, Lambda, Reals, RealVal
from kdrag.theories.real import RFun, RSeq, abs, abs_neg
from kdrag.theories.real.rseq import diff, finsum, finsum_smul, smul, sub
from kdrag.contrib.analysis._choice import axiom_of_choice
from kdrag.contrib.analysis.deriv import (
    has_deriv_at,
    has_deriv_at_sq,
    straddles,
    straddle_of_has_deriv_at,
)
from kdrag.contrib.analysis.finsum import abs_finsum_le, finsum_diff, finsum_sub
from kdrag.contrib.analysis.integral import (
    has_integral,
    integral,
    integral_eq_of_has_integral,
    is_tagged_partition,
    is_fine,
    mem_icc_of_is_tagged_partition,
    riemann_sum,
)

f, F, D = Consts("f F D", RFun)
xs, ts = Consts("xs ts", RSeq)
a, b, t, x, y, eps, delta = Reals("a b t x y eps delta")
i, n = Ints("i n")


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
    heta = l.have(Exists(y, y > 0, y * abs(b - a) + y == eps))
    l.exists(eps / (abs(b - a) + 1))
    l.auto(by=[abs.defn(b - a)])
    eta, _ = l.obtain(heta)

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
    r, _ = l.obtain(w)
    l.exists(r)
    l.beta()
    l.auto()
    l.exists(RealVal(1))
    l.beta()
    l.auto()
    hchoice = l.top_goal().ctx[-1]
    gauge_exists = l.have(Exists(D, ForAll(x, Q[x, D[x]])), by=[axiom_of_choice(Q)])
    gauge, hgauge = l.obtain(gauge_exists)
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

    # Sum the cell bounds: eta * (b - a) <= eta * |b - a| < eta * |b - a| + eta = eps.
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
