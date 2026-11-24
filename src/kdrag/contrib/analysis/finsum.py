"""Finite real sums: subtraction, telescoping, and absolute-value bounds."""

from kdrag import Theorem
from kdrag.smt import ForAll, IntVal, Reals
import kdrag.theories.int as int_
import kdrag.theories.real as real
from kdrag.theories.real.rseq import (
    a,
    b,
    n,
    i,
    m,
    cumsum,
    cumsum_succ,
    diff,
    finsum,
    finsum_succ,
    geom,
    sub,
)


@Theorem(ForAll([a, b, n], finsum(a - b, n) == finsum(a, n) - finsum(b, n)))
def finsum_sub(l):
    a, b, n = l.fixes()
    l.unfold(finsum)
    l.induct(n)
    # Each step peels one term off both sides.
    l.fix()
    l.intros()
    l.unfold(cumsum)
    l.auto(by=[sub.defn(a, b)])
    l.unfold(cumsum)
    l.auto()
    l.fix()
    l.intros()
    l.unfold(cumsum)
    l.auto(by=[sub.defn(a, b)])


@Theorem(ForAll([a, n], finsum(diff(a), n) == a[n] - a[0]))
def finsum_diff(l):
    a, n = l.fixes()
    l.unfold(finsum)
    l.induct(n)
    # Telescoping in both directions from the origin.
    l.fix()
    l.intros()
    l.unfold(cumsum)
    l.auto(by=[diff.defn(a)])
    l.unfold(cumsum)
    l.auto()
    l.fix()
    l.intros()
    l.unfold(cumsum)
    l.auto(by=[diff.defn(a)])


@Theorem(
    ForAll(
        [a, b, m, n],
        n >= 0,
        ForAll(i, m <= i, i < m + n, real.abs(a[i]) <= b[i]),
        real.abs(cumsum(a)[m + n] - cumsum(a)[m]) <= cumsum(b)[m + n] - cumsum(b)[m],
    )
)
def abs_cumsum_sub_le(l):
    """Termwise absolute bounds control the sum over a finite interval."""
    a, b, m, n = l.fixes()
    l.induct(n, using=int_.induct_nat)
    l.auto(by=[real.abs.defn(0)])
    k = l.fix()
    l.intros()
    index = m + k
    l.have(real.abs(a[index]) <= b[index], by=[])
    tail = cumsum(a)[index] - cumsum(a)[m]
    l.auto(
        by=[cumsum_succ(a, index), cumsum_succ(b, index), real.abs_add(tail, a[index])]
    )


@Theorem(
    ForAll(
        [a, b, n],
        ForAll(i, 0 <= i, i < n, real.abs(a[i]) <= b[i]),
        n >= 0,
        real.abs(finsum(a, n)) <= finsum(b, n),
    )
)
def abs_finsum_le(l):
    a, b, n = l.fixes()
    compare, nonneg = l.intros()
    zero = IntVal(0)
    within = l.have(ForAll(i, zero <= i, i < zero + n, real.abs(a[i]) <= b[i]), by=[])
    l.clear(compare)
    l.specialize(abs_cumsum_sub_le, a, b, zero, n, nonneg, within)
    l.clear(within)
    l.have(cumsum(a)[0] == 0, by=[cumsum.defn(a)])
    l.have(cumsum(b)[0] == 0, by=[cumsum.defn(b)])
    l.auto(by=[finsum.defn(a, n), finsum.defn(b, n)])


(r,) = Reals("r")


@Theorem(
    ForAll(
        [r, n],
        n >= 0,
        (1 - r) * finsum(geom(r), n) == 1 - real.pownat(r, n),
    )
)
def finsum_geom(l):
    """The sum of the first n powers, with the denominator cleared."""
    r, n = l.fixes()
    terms = geom(r)
    l.induct(n, using=int_.induct_nat)
    zero = IntVal(0)
    l.auto(by=[finsum.defn(terms, zero), cumsum.defn(terms), real.pownat_zero(r)])

    n = l.fix()
    l.intros()
    l.have(terms[n] == real.pownat(r, n), by=[geom.defn(r)])
    l.auto(by=[finsum_succ(terms, n), real.pownat_succ(r, n)])
