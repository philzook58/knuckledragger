"""Convergence and sums of real series."""

from kdrag import Theorem
from kdrag.contrib.analysis.finsum import finsum_geom
from kdrag.smt import And, ForAll, If, Int, Real, RealVal, ToReal
import kdrag.theories.int as int_
import kdrag.theories.real as real
from kdrag.theories.real.rseq import finsum, geom, has_lim, has_sum

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
    l.unfold(has_lim)
    eps = l.fix()
    l.intro()
    l.have(1 - r > 0, by=[real.abs.defn(r)])
    positive = l.have(eps * (1 - r) > 0, by=[])
    small = l.have(has_lim(geom(r), 0), by=[has_lim_geom_zero(r)])
    l.unfold(has_lim, at=small)
    small = l.top_goal().ctx[-1]
    cutoff = l.obtain(l.specialize(small, eps * (1 - r), positive))
    near = l.top_goal().ctx[-1]
    l.exists(If(cutoff > 0, cutoff, 0))
    n = l.fix()
    l.intro()
    beyond = l.have(n > cutoff, by=[])
    l.have(n >= 0, by=[])
    l.specialize(near, n, beyond)
    partial = finsum(geom(r), n)
    power = real.pownat(r, n)
    l.have(real.abs(power) < eps * (1 - r), by=[geom.defn(r)])
    l.have((1 - r) * (partial - 1 / (1 - r)) == -power, by=[finsum_geom(r, n)])
    l.have(
        real.abs(partial - 1 / (1 - r)) < eps,
        by=[
            real.abs_mul(1 - r, partial - 1 / (1 - r)),
            real.abs_neg(power),
            real.abs.defn(1 - r),
        ],
    )
    l.auto(by=[finsum.defn(geom(r), n)])
