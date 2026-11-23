"""Convergence and sums of real series."""

from kdrag import Theorem
from kdrag.contrib.analysis.finsum import finsum_geom
from kdrag.contrib.analysis.rseq import (
    abs_sub_le_of_has_lim,
    has_lim_congr_nonneg,
    lim_lemma,
)
from kdrag.smt import (
    And,
    Consts,
    Exists,
    ForAll,
    Int,
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
    add,
    cumsum,
    cumsum_add,
    cumsum_mono,
    cumsum_succ,
    exists_has_lim_of_monotone_of_bdd_above,
    finsum,
    geom,
    has_lim,
    has_lim_sub,
    has_sum,
    is_monotone,
    range_nonneg,
    sub,
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
    positive = a + magnitude
    h = l.have(
        Exists(S, has_sum(magnitude, S)),
        by=[exists_has_sum_of_nonneg_of_bounded(magnitude, M), abs_ext, real.abs_pos],
    )
    mag_sum, _ = l.obtain(h)
    l.have(ForAll(n, positive[n] >= 0))
    j = l.fix()
    l.auto(by=[add.defn(a, magnitude), abs_ext(a, j), real.abs.defn(a[j])])
    l.have(ForAll(n, n >= 0, cumsum(positive)[n] <= 2 * M))
    j = l.fix()
    l.intro()
    l.have(
        cumsum(a)[j] <= cumsum(magnitude)[j],
        by=[cumsum_mono(a, magnitude, j), abs_ext, real.abs.defn],
    )
    l.auto(by=[cumsum_add(a, magnitude, j), add.defn(cumsum(a), cumsum(magnitude))])
    h = l.have(
        Exists(S, has_sum(positive, S)),
        by=[exists_has_sum_of_nonneg_of_bounded(positive, 2 * M)],
    )
    pos_sum, _ = l.obtain(h)
    l.exists(pos_sum - mag_sum)
    l.have(cumsum(positive) - cumsum(magnitude) == cumsum(a))
    l.ext()
    j = l.fix()
    l.auto(
        by=[
            cumsum_add(a, magnitude, j),
            add.defn(cumsum(a), cumsum(magnitude)),
            sub.defn(cumsum(positive), cumsum(magnitude)),
        ]
    )
    l.auto(
        by=[
            has_sum.defn,
            has_lim_sub(cumsum(positive), cumsum(magnitude), pos_sum, mag_sum),
        ]
    )


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
        Exists(S, has_sum(a, S)),
    )
)
def exists_has_sum_of_geometric_decay(l):
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
    l.have(ForAll(n, n >= 0, partial[n] <= bound))
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
