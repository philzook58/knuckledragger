"""Convergence and sums of real series."""

from kdrag import Theorem
from kdrag.contrib.analysis.finsum import finsum_geom
from kdrag.contrib.analysis.rseq import has_lim_congr_nonneg, lim_lemma
from kdrag.smt import And, ForAll, Int, Lambda, Real, RealVal, ToReal
import kdrag.theories.int as int_
import kdrag.theories.real as real
from kdrag.theories.real.rseq import cumsum, finsum, geom, has_lim, has_sum


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
    cutoff = l.obtain(large)
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
