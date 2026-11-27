"""Convergence and sums of real series."""

from kdrag import Theorem
from kdrag.contrib.analysis.cauchy import is_cauchy_iff_exists_has_lim
from kdrag.contrib.analysis.finsum import abs_cumsum_sub_le, finsum_diff, finsum_geom
from kdrag.contrib.analysis.rseq import (
    abs_sub_le_of_has_lim,
    has_lim_congr_nonneg,
    lim_lemma,
)
from kdrag.smt import (
    And,
    Consts,
    Eq,
    Exists,
    ForAll,
    If,
    Int,
    IntVal,
    Lambda,
    Real,
    RealVal,
    ToReal,
)
import kdrag.theories.int as int_
import kdrag.theories.real as real
from kdrag.theories.real import RSeq, rset
from kdrag.theories.real.rseq import (
    abs as seq_abs,
    abs_ext,
    cumsum,
    cumsum_succ,
    diff,
    eventually,
    eventually_near,
    exists_has_lim_of_monotone_of_bdd_above,
    finsum,
    geom,
    has_lim,
    has_sum,
    is_cauchy,
    is_monotone,
    is_summable,
    i,
    near,
    range_nonneg,
)

r = Real("r")
n = Int("n")


@Theorem(
    ForAll(
        [r, n],
        real.abs(r) <= 1,
        n >= 0,
        (1 + ToReal(n) * (1 - real.abs(r))) * real.abs(real.pownat(r, n)) <= 1,
    )
)
def geom_power_bound(l):
    """Bound geometric decay by a reciprocal linear function of the index."""
    r, n = l.fixes()
    l.intro()
    rho = real.abs(r)
    gap = 1 - rho
    l.induct(n, using=int_.induct_nat)
    l.auto(by=[real.pownat_zero(r), real.abs.defn(1)])

    n = l.fix()
    l.intros()
    power = real.pownat(r, n)
    next_power = real.pownat(r, n + 1)
    l.have(
        real.abs(next_power) == rho * real.abs(power),
        by=[real.pownat_succ(r, n), real.abs_mul(r, power)],
    )
    # The factor at n+1, after multiplying by rho, is no larger than at n.
    l.have(
        (1 + ToReal(n + 1) * gap) * rho <= 1 + ToReal(n) * gap,
        by=[real.abs_pos(r)],
    )
    l.auto(by=[real.abs_pos(power)])


@Theorem(ForAll(r, real.abs(r) < 1, has_lim(geom(r), 0)))
def has_lim_geom_zero(l):
    r = l.fix()
    l.intro()
    l.unfold(has_lim)
    eps = l.fix()
    l.intro()
    gap = 1 - real.abs(r)
    # Choose a cutoff with eps * gap * N > 1.
    positive = l.have(And(eps * gap > 0, RealVal(1) > 0), by=[])
    large = l.specialize(real.archimedes, eps * gap, 1, positive)
    cutoff, _ = l.obtain(large)
    l.exists(cutoff)
    n = l.fix()
    l.intro()
    l.have(n >= 0, by=[])
    l.have(eps * (1 + ToReal(n) * gap) > 1, by=[])
    power = real.pownat(r, n)
    l.have(geom(r)[n] == power, by=[geom.defn(r)])
    l.auto(by=[geom_power_bound(r, n)])


@Theorem(ForAll(r, real.abs(r) < 1, has_sum(geom(r), 1 / (1 - r))))
def has_sum_geom(l):
    r = l.fix()
    l.intro()
    l.unfold(has_sum)

    powers = geom(r)
    total = 1 / (1 - r)
    expression = (1 - powers[n]) / (1 - r)
    closed_form = Lambda(n, expression)
    l.have(1 - r != 0, by=[real.abs.defn(r)])
    l.have(
        has_lim(closed_form, total),
        by=[lim_lemma(expression, n)(0), has_lim_geom_zero(r)],
    )

    # Identify each partial sum with its closed form.
    partial_sums = cumsum(powers)
    l.have(ForAll(n, n >= 0, closed_form[n] == partial_sums[n]))
    index = l.fix()
    l.intro()
    l.auto(
        by=[
            geom.defn(r),
            finsum.defn(powers, index),
            finsum_geom(r, index),
        ]
    )
    l.auto(by=[has_lim_congr_nonneg(closed_form, partial_sums, total)])


a, b = Consts("a b", RSeq)
m, start = Int("m"), Int("start")
M, S = Real("M"), Real("S")


eps = Real("eps")


def _cauchy_tails(a):
    return ForAll(
        eps,
        eps > 0,
        Exists(
            start,
            start >= 0,
            ForAll(
                [m, n],
                start <= m,
                m <= n,
                real.abs(cumsum(a)[n] - cumsum(a)[m]) < eps,
            ),
        ),
    )


@Theorem(ForAll(a, Eq(is_cauchy(cumsum(a)), _cauchy_tails(a))))
def _is_cauchy_cumsum_iff_tails(l):
    a = l.fix()
    partial = cumsum(a)
    l.unfold(is_cauchy)
    l.split()

    # Move the strict Cauchy cutoff to a nonnegative inclusive cutoff.
    cauchy = l.intro()
    eps = l.fix()
    positive = l.intro()
    N, close = l.obtain(l.specialize(cauchy, eps, positive))
    l.exists(If(N < 0, IntVal(0), N + 1))
    l.split()
    l.auto()
    m, n = l.fixes()
    l.intros()
    l.specialize(close, n, m)
    l.auto()

    # The unordered Cauchy condition follows by swapping the two endpoints.
    tails = l.intro()
    eps = l.fix()
    positive = l.intro()
    N, bound = l.obtain(l.specialize(tails, eps, positive))
    _, small = l.andE(bound)
    l.exists(N)
    m, n = l.fixes()
    l.intros()
    l.cases(n <= m, m < n)
    l.specialize(small, n, m)
    l.auto()
    l.specialize(small, m, n)
    l.auto(by=[real.abs_neg(partial[n] - partial[m])])


@Theorem(ForAll(a, Eq(is_summable(a), is_cauchy(cumsum(a)))))
def is_summable_iff_is_cauchy_cumsum(l):
    """A real series converges iff its partial sums form a Cauchy sequence."""
    a = l.fix()
    partial = cumsum(a)
    l.split()
    l.unfold(is_summable)
    value, _ = l.obtain(l.intro())
    l.have(has_lim(partial, value), by=[has_sum.defn(a, value)])
    l.have(Exists(S, has_lim(partial, S)))
    l.exists(value)
    l.auto()
    l.auto(by=[is_cauchy_iff_exists_has_lim(partial)])

    l.intro()
    converges = l.have(
        Exists(S, has_lim(partial, S)), by=[is_cauchy_iff_exists_has_lim(partial)]
    )
    value, _ = l.obtain(converges)
    l.unfold(is_summable)
    l.exists(value)
    l.auto(by=[has_sum.defn(a, value)])


@Theorem(ForAll(a, is_cauchy(cumsum(diff(a))), is_cauchy(a)))
def _is_cauchy_of_is_cauchy_cumsum_diff(l):
    a = l.fix()
    d = diff(a)
    l.unfold(is_cauchy)
    tails = l.intro()
    eps = l.fix()
    positive = l.intro()
    N, close = l.obtain(l.specialize(tails, eps, positive))
    l.exists(N)
    j, k = l.fixes()
    l.intros()
    l.specialize(close, j, k)
    # Telescoping cancels the common initial value a[0].
    l.auto(
        by=[finsum.defn(d, j), finsum_diff(a, j), finsum.defn(d, k), finsum_diff(a, k)]
    )


@Theorem(ForAll(a, is_summable(diff(a)), is_cauchy(a)))
def is_cauchy_of_is_summable_diff(l):
    """Summable successive differences make the sequence Cauchy."""
    a = l.fix()
    l.intro()
    l.auto(
        by=[
            is_summable_iff_is_cauchy_cumsum(diff(a)),
            _is_cauchy_of_is_cauchy_cumsum_diff(a),
        ]
    )


@Theorem(ForAll(a, Eq(is_summable(a), _cauchy_tails(a))))
def is_summable_iff_cauchy_tails(l):
    """A real series converges iff every sufficiently late finite tail is small."""
    a = l.fix()
    l.auto(by=[is_summable_iff_is_cauchy_cumsum(a), _is_cauchy_cumsum_iff_tails(a)])


@Theorem(
    ForAll(
        [a, b, start],
        ForAll(n, n >= start, real.abs(a[n]) <= b[n]),
        is_summable(b),
        is_summable(a),
    )
)
def is_summable_of_eventually_abs_le(l):
    """A summable upper bound on the magnitudes controls every late tail."""
    a, b, start = l.fixes()
    dominates, _ = l.intros()
    tails = l.have(_cauchy_tails(b), by=[is_summable_iff_cauchy_tails(b)])
    l.rw(is_summable_iff_cauchy_tails(a))
    eps = l.fix()
    positive = l.intro()
    N, bound = l.obtain(l.specialize(tails, eps, positive))
    _, small = l.andE(bound)
    l.exists(If(N < start, start, N))
    l.split()
    l.auto()
    m, n = l.fixes()
    l.intros()
    within = l.have(ForAll(i, m <= i, i < m + (n - m), real.abs(a[i]) <= b[i]))
    j = l.fix()
    l.intros()
    l.specialize(dominates, j)
    l.auto()
    l.specialize(small, m, n)
    length_nonneg = l.have(n - m >= 0, by=[])
    l.specialize(abs_cumsum_sub_le, a, b, m, n - m, length_nonneg, within)
    l.auto(by=[real.abs.defn(cumsum(b)[n] - cumsum(b)[m])])


@Theorem(
    ForAll(
        [a, b, start],
        ForAll(n, n >= start, And(a[n] >= 0, a[n] <= b[n])),
        is_summable(b),
        is_summable(a),
    )
)
def is_summable_of_nonneg_of_le(l):
    """The comparison test for eventually nonnegative series."""
    a, b, start = l.fixes()
    compare, _ = l.intros()
    l.have(ForAll(n, n >= start, real.abs(a[n]) <= b[n]))
    j = l.fix()
    l.intro()
    l.specialize(compare, j)
    l.auto(by=[real.abs_if_pos(a[j])])
    l.auto(by=[is_summable_of_eventually_abs_le(a, b, start)])


@Theorem(ForAll(a, is_summable(seq_abs(a)), is_summable(a)))
def is_summable_of_abs(l):
    """Absolute convergence implies convergence."""
    a = l.fix()
    l.intro()
    l.have(ForAll(n, n >= 0, real.abs(a[n]) <= seq_abs(a)[n]), by=[abs_ext])
    l.auto(by=[is_summable_of_eventually_abs_le(a, seq_abs(a), 0)])


@Theorem(
    ForAll(
        [a, m, n],
        ForAll(start, a[start] >= 0),
        m <= n,
        cumsum(a)[m] <= cumsum(a)[n],
    )
)
def cumsum_monotone_of_nonneg(l):
    a, m, n = l.fixes()
    l.intro()
    # Induct on the distance between the indices.
    bound = l.have(ForAll(n, n >= 0, cumsum(a)[m] <= cumsum(a)[m + n]))
    distance = l.fix()
    l.intro()
    l.induct(distance, using=int_.induct_nat)
    l.auto()
    distance = l.fix()
    l.intros()
    l.auto(by=[cumsum_succ(a, m + distance)])
    l.auto()
    l.intro()
    nonneg = l.have(n - m >= 0, by=[])
    l.specialize(bound, n - m, nonneg)
    l.auto()


@Theorem(
    ForAll(
        [a, M],
        ForAll(n, a[n] >= 0),
        ForAll(n, n >= 0, cumsum(a)[n] <= M),
        Exists(S, has_sum(a, S)),
    )
)
def exists_has_sum_of_nonneg_of_bounded(l):
    a, M = l.fixes()
    l.intros()
    partial = cumsum(a)
    values = range_nonneg(partial)
    l.have(
        is_monotone(partial), by=[is_monotone.defn(partial), cumsum_monotone_of_nonneg]
    )
    l.have(rset.bdd_above(values))
    l.unfold(rset.bdd_above)
    l.exists(M)
    l.auto(by=[rset.is_ub.defn(values, M), range_nonneg.defn(partial)])
    l.unfold(has_sum)
    l.auto(by=[exists_has_lim_of_monotone_of_bdd_above(partial)])


@Theorem(
    ForAll(
        [a, M],
        ForAll(n, n >= 0, cumsum(seq_abs(a))[n] <= M),
        Exists(S, has_sum(a, S)),
    )
)
def exists_has_sum_of_abs_prefix_bound(l):
    a, M = l.fixes()
    l.intro()
    magnitude = seq_abs(a)
    l.have(is_summable(magnitude))
    l.unfold(is_summable)
    l.auto(
        by=[exists_has_sum_of_nonneg_of_bounded(magnitude, M), abs_ext, real.abs_pos]
    )
    l.have(is_summable(a), by=[is_summable_of_abs(a)])
    l.auto(by=[is_summable.defn(a)])


@Theorem(
    ForAll(
        [a, r, start, n],
        0 <= r,
        r < 1,
        ForAll(m, m >= start, real.abs(a[m + 1]) <= r * real.abs(a[m])),
        n >= 0,
        (1 - r) * real.abs(cumsum(a)[start + n] - cumsum(a)[start])
        + real.abs(a[start + n])
        <= real.abs(a[start]),
    )
)
def geometric_tail_bound(l):
    """The amount spent plus the remaining geometric budget never increases."""
    a, r, start, n = l.fixes()
    l.intro()
    l.intro()
    decay = l.intro()
    l.induct(n, using=int_.induct_nat)
    l.auto(by=[real.abs.defn(0)])
    n = l.fix()
    l.intros()
    index = start + n
    beyond = l.have(index >= start, by=[])
    l.specialize(decay, index, beyond)
    partial = cumsum(a)
    error = partial[index] - partial[start]
    next_error = partial[index + 1] - partial[start]
    l.have(next_error == error + a[index], by=[cumsum_succ(a, index)])
    l.have(
        real.abs(next_error) <= real.abs(error) + real.abs(a[index]),
        by=[real.abs_add(error, a[index])],
    )
    l.auto()


@Theorem(
    ForAll(
        [a, r, start],
        0 <= r,
        r < 1,
        ForAll(m, m >= start, real.abs(a[m + 1]) <= r * real.abs(a[m])),
        Exists(M, ForAll(n, n >= 0, cumsum(seq_abs(a))[n] <= M)),
    )
)
def exists_abs_prefix_bound_of_geometric_decay(l):
    a, r, start = l.fixes()
    l.intro()
    l.intro()
    decay = l.intro()
    magnitude = seq_abs(a)
    partial = cumsum(magnitude)
    l.have(ForAll(n, magnitude[n] >= 0))
    j = l.fix()
    l.auto(by=[abs_ext(a, j), real.abs_pos(a[j])])
    l.have(
        ForAll(m, m >= start, real.abs(magnitude[m + 1]) <= r * real.abs(magnitude[m]))
    )
    j = l.fix()
    beyond = l.intro()
    l.specialize(decay, j, beyond)
    l.auto(
        by=[
            abs_ext(a, j),
            abs_ext(a, j + 1),
            real.abs.defn(magnitude[j]),
            real.abs.defn(magnitude[j + 1]),
        ]
    )
    bound = partial[start] + magnitude[start] / (1 - r)
    l.exists(bound)
    j = l.fix()
    l.intro()
    l.cases(j >= start)
    offset = j - start
    l.have(start + offset == j, by=[])
    l.have(
        (1 - r) * real.abs(partial[j] - partial[start]) + real.abs(magnitude[j])
        <= real.abs(magnitude[start]),
        by=[geometric_tail_bound(magnitude, r, start, offset)],
    )
    l.auto(
        by=[
            real.abs.defn(partial[j] - partial[start]),
            real.abs.defn(magnitude[start]),
            real.abs_pos(magnitude[j]),
        ]
    )
    l.auto(by=[cumsum_monotone_of_nonneg(magnitude, j, start)])


@Theorem(
    ForAll(
        [a, r, start],
        0 <= r,
        r < 1,
        ForAll(m, m >= start, real.abs(a[m + 1]) <= r * real.abs(a[m])),
        Exists(S, has_sum(a, S)),
    )
)
def exists_has_sum_of_geometric_decay(l):
    a, r, start = l.fixes()
    l.intros()
    h = l.have(
        Exists(M, ForAll(n, n >= 0, cumsum(seq_abs(a))[n] <= M)),
        by=[exists_abs_prefix_bound_of_geometric_decay(a, r, start)],
    )
    bound, _ = l.obtain(h)
    l.auto(by=[exists_has_sum_of_abs_prefix_bound(a, bound)])


@Theorem(
    ForAll(
        [a, r, start, S],
        0 <= r,
        r < 1,
        ForAll(m, m >= start, real.abs(a[m + 1]) <= r * real.abs(a[m])),
        has_sum(a, S),
        real.abs(S - cumsum(a)[start]) <= real.abs(a[start]) / (1 - r),
    )
)
def has_sum_error_of_geometric_decay(l):
    a, r, start, S = l.fixes()
    l.intros()
    partial = cumsum(a)
    bound = real.abs(a[start]) / (1 - r)
    l.have(ForAll(n, n >= start, real.abs(partial[n] - partial[start]) <= bound))
    index = l.fix()
    l.intro()
    offset = index - start
    l.have(
        (1 - r) * real.abs(partial[index] - partial[start]) + real.abs(a[index])
        <= real.abs(a[start]),
        by=[geometric_tail_bound(a, r, start, offset)],
    )
    l.auto(by=[real.abs_pos(a[index])])

    l.auto(
        by=[
            has_sum.defn(a, S),
            abs_sub_le_of_has_lim(partial, S, partial[start], bound, start),
        ]
    )


@Theorem(
    ForAll(
        [a, r],
        eventually(Lambda(n, a[n] != 0)),
        has_lim(Lambda(n, real.abs(a[n + 1] / a[n])), r),
        r < 1,
        And(is_summable(a), is_summable(seq_abs(a))),
    )
)
def summable_of_ratio_test(l):
    """An eventual nonzero denominator and a ratio limit below one imply absolute convergence."""
    a, r = l.fixes()
    ratios = Lambda(n, real.abs(a[n + 1] / a[n]))
    l.intros()
    cutoff_var = Int("N")
    nonzero = l.have(
        Exists(cutoff_var, ForAll(n, n > cutoff_var, a[n] != 0)),
        by=[eventually.defn(Lambda(n, a[n] != 0))],
    )
    nonzero_cutoff, nonzero_tail = l.obtain(nonzero)
    q = (1 + real.max(0, r)) / 2
    l.have(0 <= q, by=[real.max.defn(0, r)])
    l.have(q < 1, by=[real.max.defn(0, r)])
    l.have(q - r > 0, by=[real.max.defn(0, r)])
    close = l.have(
        Exists(cutoff_var, ForAll(n, n > cutoff_var, real.abs(ratios[n] - r) < q - r)),
        by=[eventually_near(ratios, r, q - r), eventually.defn(near(ratios, r, q - r))],
    )
    ratio_cutoff, near_ratio = l.obtain(close)
    start = If(nonzero_cutoff > ratio_cutoff, nonzero_cutoff, ratio_cutoff) + 1
    l.have(ForAll(n, n >= start, real.abs(a[n + 1]) <= q * real.abs(a[n])))
    index = l.fix()
    l.intro()
    beyond_nonzero = l.have(index > nonzero_cutoff, by=[])
    beyond_ratio = l.have(index > ratio_cutoff, by=[])
    l.specialize(nonzero_tail, index, beyond_nonzero)
    l.specialize(near_ratio, index, beyond_ratio)
    l.have(
        real.abs(a[index + 1] / a[index]) < q,
        by=[real.abs.defn(real.abs(a[index + 1] / a[index]) - r)],
    )
    l.auto(by=[real.abs_div(a[index + 1], a[index]), real.abs_pos_iff(a[index])])

    h = l.have(
        Exists(M, ForAll(n, n >= 0, cumsum(seq_abs(a))[n] <= M)),
        by=[exists_abs_prefix_bound_of_geometric_decay(a, q, start)],
    )
    bound, _ = l.obtain(h)
    l.unfold(is_summable)
    l.split()
    l.auto(by=[exists_has_sum_of_abs_prefix_bound(a, bound)])
    l.auto(
        by=[
            exists_has_sum_of_nonneg_of_bounded(seq_abs(a), bound),
            abs_ext,
            real.abs_pos,
        ]
    )
