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
    cumsum,
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
        [a, b, n],
        ForAll(i, 0 <= i, i < n, real.abs(a[i]) <= b[i]),
        n >= 0,
        real.abs(finsum(a, n)) <= finsum(b, n),
    )
)
def abs_finsum_le(l):
    a, b, n = l.fixes()
    # Keep the termwise bound in the induction motive.
    l.induct(n, using=int_.induct_nat)
    l.auto(by=[finsum.defn, cumsum.defn, real.abs.defn])
    n = l.fix()
    l.intros()
    l.have(real.abs(a[n]) <= b[n], by=[])
    # Triangle inequality on the newest term.
    l.auto(by=[finsum_succ(a, n), finsum_succ(b, n), real.abs_add(finsum(a, n), a[n])])


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
