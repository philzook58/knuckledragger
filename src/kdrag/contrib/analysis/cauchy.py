"""The Cauchy criterion for real sequences."""

from kdrag import Theorem, prove
from kdrag.smt import Eq, Exists, ForAll, If, IntVal, RealVal
import kdrag.theories.real as real
import kdrag.theories.real.rseq as seq
from kdrag.theories.real.rseq import F, a, has_lim, is_cauchy, n, x

from .subsequence import (
    bolzano_weierstrass,
    is_bounded_nonneg,
    is_subseq_index,
    le_subseq_index,
)


@Theorem(ForAll([a, x], has_lim(a, x), is_cauchy(a)))
def is_cauchy_of_has_lim(l):
    a, x = l.fixes()
    l.unfold(has_lim, is_cauchy)
    limits = l.intro()
    eps = l.fix()
    l.intro()
    positive = l.have(eps / 2 > 0, by=[])
    N, close = l.obtain(l.specialize(limits, eps / 2, positive))
    # After one cutoff both terms are within eps/2 of the same limit.
    l.exists(N)
    i, j = l.fixes()
    l.intros()
    l.specialize(close, i, keep=True)
    l.specialize(close, j)
    l.auto(by=[real.abs_triangle(a[i], a[j], x), real.abs_neg(a[j] - x)])


@Theorem(ForAll(a, is_cauchy(a), is_bounded_nonneg(a)))
def is_bounded_nonneg_of_is_cauchy(l):
    a = l.fix()
    l.unfold(is_cauchy)
    tails = l.intro()
    N, close = l.obtain(l.specialize(tails, 1, prove(RealVal(1) > 0)))
    end = If(N < 0, IntVal(0), N + 1)
    prefix_bound = seq.finsum(seq.abs(a), end)
    tail_bound = real.abs(a[end]) + 1
    l.have(prefix_bound >= 0, by=[seq.finsum_nonneg(seq.abs(a), end), seq.abs_ge_0])
    l.have(tail_bound >= 0, by=[real.abs_pos(a[end])])
    l.unfold(is_bounded_nonneg)
    l.exists(prefix_bound + tail_bound)
    j = l.fix()
    l.intro()
    l.cases(j < end, j >= end)
    # The finite prefix is bounded by the sum of its absolute values.
    l.have(
        ForAll(n, n >= 0, n < end, seq.abs(a)[n] <= prefix_bound),
        by=[seq.abs_le_finsum_abs(a, end)],
    )
    l.auto(by=[seq.abs_ext(a, j)])
    # Every tail term lies within 1 of the first term of the tail.
    l.specialize(close, j, end)
    l.auto(by=[real.abs_triangle(a[j], 0, a[end])])


@Theorem(
    ForAll(
        [a, F, x],
        is_cauchy(a),
        is_subseq_index(F),
        has_lim(seq.dommap(F, a), x),
        has_lim(a, x),
    )
)
def has_lim_of_is_cauchy_of_subseq(l):
    a, idx, x = l.fixes()
    l.unfold(is_cauchy, has_lim)
    tails, _, limits = l.intros()
    eps = l.fix()
    l.intro()
    positive = l.have(eps / 2 > 0, by=[])
    N, close = l.obtain(l.specialize(tails, eps / 2, positive))
    K, subseq_close = l.obtain(l.specialize(limits, eps / 2, positive))
    # Pick one subsequence term late enough for both estimates.
    j = If(N < K, K, N) + 1
    j = If(j < 0, IntVal(0), j)
    l.have(idx[j] >= j, by=[le_subseq_index(idx, j)])
    l.specialize(subseq_close, j)
    l.have(real.abs(a[idx[j]] - x) < eps / 2, by=[seq.dommap.defn(idx, a)])
    l.exists(N)
    i = l.fix()
    l.intro()
    l.specialize(close, i, idx[j])
    l.auto(by=[real.abs_triangle(a[i], x, a[idx[j]])])


@Theorem(ForAll(a, Eq(is_cauchy(a), Exists(x, has_lim(a, x)))))
def is_cauchy_iff_exists_has_lim(l):
    a = l.fix()
    l.split()
    cauchy = l.intro()
    bounded = l.specialize(is_bounded_nonneg_of_is_cauchy, a, cauchy)
    (idx, limit), _ = l.obtain(l.specialize(bolzano_weierstrass, a, bounded))
    l.exists(limit)
    l.auto(by=[has_lim_of_is_cauchy_of_subseq(a, idx, limit)])

    converges = l.intro()
    limit, _ = l.obtain(converges)
    l.auto(by=[is_cauchy_of_has_lim(a, limit)])
