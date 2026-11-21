import kdrag as kd
from kdrag import smt
from kdrag.theories.real import rseq
from kdrag.theories.real import rset


def test_oriented_partial_sums_on_both_sides_of_zero():
    n = smt.Int("n")
    a = smt.Lambda(n, smt.ToReal(n) + 3)
    # S[n] sums [0,n) forward and negates [n,0) backward.
    for index, expected in ((-3, -3), (-2, -3), (-1, -2), (0, 0), (1, 3), (2, 7)):
        kd.prove(rseq.cumsum(a)[index] == expected, by=[rseq.cumsum.defn(a)])


def test_finite_sum_excludes_the_upper_endpoint():
    a = smt.Store(smt.K(smt.IntSort(), smt.RealVal(0)), 2, 7)
    kd.prove(rseq.finsum(a, 2) == 0, by=[rseq.finsum.defn, rseq.cumsum.defn(a)])
    kd.prove(rseq.finsum(a, 3) == 7, by=[rseq.finsum.defn, rseq.cumsum.defn(a)])


def test_monotone_step_sequence_converges_to_its_supremum():
    n = smt.Int("n")
    a = smt.Lambda(n, smt.If(n < 2, smt.RealVal(0), smt.RealVal(1)))
    one = smt.RealVal(1)
    values = rseq.range_nonneg(a)
    monotone = kd.prove(rseq.is_monotone(a), by=[rseq.is_monotone.defn(a)])
    supremum = kd.prove(
        rset.is_lub(values, one),
        by=[rset.is_lub.defn, rset.is_ub.defn, rseq.range_nonneg.defn(a)],
    )
    limit = rseq.has_lim_of_monotone_of_is_lub(a, one)(monotone, supremum)
    kd.prove(rseq.has_lim(a, one), by=[limit])
