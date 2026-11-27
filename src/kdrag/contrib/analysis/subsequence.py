"""Subsequences of real sequences and the Bolzano–Weierstrass theorem."""

import kdrag as kd
from kdrag import Theorem, define
from kdrag.smt import (
    And,
    Exists,
    ForAll,
    If,
    Implies,
    IntSort,
    IntVal,
    Lambda,
    Not,
    RealVal,
    Reals,
)
import kdrag.theories.int as int_
import kdrag.theories.real as real
from kdrag.theories.real import rset
from kdrag.theories.real.rseq import (
    F,
    a,
    dommap,
    eventually,
    eventually_near,
    has_lim,
    has_lim_inv,
    k,
    m,
    n,
    near,
)

from ._int_recursion import int_recursion

B, eps, s, t = Reals("M eps s t")

is_subseq_index = define(
    "analysis.is_subseq_index",
    F,
    And(F[0] >= 0, ForAll(n, n >= 0, F[n] < F[n + 1])),
)
is_bounded_nonneg = define(
    "analysis.is_bounded_nonneg",
    a,
    Exists(B, ForAll(n, n >= 0, real.abs(a[n]) <= B)),
)


@Theorem(ForAll([F, n], is_subseq_index(F), n >= 0, n <= F[n]))
def le_subseq_index(l):
    """The nth index of a subsequence is at least n."""
    idx, n = l.fixes()
    l.intros()
    l.have(idx[0] >= 0, by=[is_subseq_index.defn(idx)])
    step = l.have(
        ForAll(n, n >= 0, idx[n] < idx[n + 1]), by=[is_subseq_index.defn(idx)]
    )
    l.induct(n, using=int_.induct_nat)
    l.auto()
    j = l.fix()
    l.intros()
    l.specialize(step, j)
    l.auto()


# A level is exceeded arbitrarily late if no cutoff bounds all later terms by it.
_is_late_level = define(
    "analysis.is_late_level", [a, t], ForAll(m, Exists(k, k > m, t < a[k]))
)


_cluster = define(
    "analysis.is_subseq_cluster",
    [a, s],
    ForAll([eps, m], eps > 0, Exists(k, k > m, real.abs(a[k] - s) < eps)),
)


@Theorem(ForAll(a, is_bounded_nonneg(a), Exists(s, _cluster(a, s))))
def _exists_cluster(l):
    a = l.fix()
    l.unfold(is_bounded_nonneg)
    M, bound = l.obtain(l.intro())
    levels = Lambda(t, _is_late_level(a, t))

    # The bounded sequence has a nonempty, bounded set of late levels.
    l.have(_is_late_level(a, -M - 1))
    l.unfold(_is_late_level)
    j = l.fix()
    index = If(j < 0, IntVal(0), j + 1)
    l.exists(index)
    l.specialize(bound, index)
    l.auto(by=[real.abs_le(a[index], M)])
    l.have(Exists(t, levels[t]))
    l.exists(-M - 1)
    l.auto()

    l.have(rset.is_ub(levels, M))
    l.unfold(rset.is_ub)
    level = l.fix()
    l.intro()
    late = l.have(
        ForAll(m, Exists(k, k > m, level < a[k])), by=[_is_late_level.defn(a, level)]
    )
    hit = l.specialize(late, 0)
    j, _ = l.obtain(hit)
    l.specialize(bound, j)
    l.auto(by=[real.abs_le(a[j], M)])

    l.have(rset.bdd_above(levels), by=[rset.bdd_above.defn(levels)])
    sup = l.have(
        Exists(s, rset.is_lub(levels, s)), by=[rset.exists_is_lub_of_bdd_above(levels)]
    )
    limit, _ = l.obtain(sup)
    l.clear(bound)
    l.exists(limit)
    l.unfold(_cluster)
    eps, cutoff = l.fixes()
    l.intro()
    # Above the supremum plus half the error, there are no late terms.
    hi, lo = limit + eps / 2, limit - eps / 2
    l.have(rset.is_ub(levels, limit), by=[rset.is_ub_of_is_lub(levels, limit)])
    l.have(Not(levels[hi]), by=[rset.le_of_mem_of_is_ub(levels, hi, limit)])
    upper = l.have(
        Exists(m, ForAll(k, k > m, a[k] <= hi)), by=[_is_late_level.defn(a, hi)]
    )
    end, upper_tail = l.obtain(upper)
    # Below the supremum minus half the error, some level is still exceeded.
    l.have(
        Not(rset.is_ub(levels, lo)), by=[rset.le_of_is_lub_of_is_ub(levels, limit, lo)]
    )
    lower = l.have(Exists(t, levels[t], lo < t), by=[rset.is_ub.defn(levels, lo)])
    level, _ = l.obtain(lower)
    start = If(cutoff < end, end, cutoff)
    late = l.have(
        ForAll(m, Exists(k, k > m, level < a[k])), by=[_is_late_level.defn(a, level)]
    )
    hit = l.specialize(late, start)
    j, _ = l.obtain(hit)
    l.specialize(upper_tail, j)
    l.exists(j)
    l.auto(by=[real.abs.defn(a[j] - limit)])


@Theorem(
    ForAll(
        [a, s, n, m],
        Exists(
            k,
            Implies(
                And(_cluster(a, s), n > 0),
                And(k > m, real.abs(a[k] - s) < RealVal(1) / n),
            ),
        ),
    )
)
def _exists_next_index(l):
    """Choose a later approximation with error below 1/n."""
    a, s, n, cutoff = l.fixes()
    l.cases(And(_cluster(a, s), n > 0))
    radius = RealVal(1) / n
    positive = l.have(radius > 0, by=[])
    approximations = l.have(
        ForAll([eps, m], eps > 0, Exists(k, k > m, real.abs(a[k] - s) < eps)),
        by=[_cluster.defn(a, s)],
    )
    j, _ = l.obtain(l.specialize(approximations, radius, cutoff, positive))
    l.exists(j)
    l.auto()
    l.exists(cutoff + 1)
    l.auto()


(_next_index,), _next_index_spec = kd.kernel.choose(_exists_next_index)
(_indices,), _indices_spec = kd.kernel.choose(int_recursion(IntSort()))


@Theorem(
    ForAll(
        [a, s],
        _cluster(a, s),
        Exists(F, And(is_subseq_index(F), has_lim(dommap(F, a), s))),
    )
)
def _exists_subseq_of_cluster(l):
    a, s = l.fixes()
    l.intro()
    step = Lambda([n, m], _next_index(a, s, n + 1, m))
    idx = _indices(step, 0)
    initial, recurrence = l.andE(l.specialize(_indices_spec, step, 0))
    l.specialize(initial, 0)
    # Iteration gives both a strictly later index and the required accuracy.
    steps = l.have(
        ForAll(
            n,
            n >= 0,
            And(
                idx[n] < idx[n + 1], real.abs(a[idx[n + 1]] - s) < RealVal(1) / (n + 1)
            ),
        )
    )
    j = l.fix()
    l.intro()
    l.specialize(recurrence, j)
    l.auto(by=[_next_index_spec(a, s, j + 1, idx[j])])

    l.clear(recurrence)
    l.exists(idx)
    l.split()
    l.unfold(is_subseq_index)
    l.split()
    l.auto()
    j = l.fix()
    l.intro()
    l.specialize(steps, j)
    l.auto()
    l.unfold(has_lim, dommap)
    eps = l.fix()
    l.intro()
    inv = Lambda(n, RealVal(1) / n)
    close = near(inv, RealVal(0), eps)
    l.have(eventually(close), by=[has_lim_inv, eventually_near(inv, RealVal(0), eps)])
    small = l.have(eventually.defn(close).thm.arg(1), by=[eventually.defn(close)])
    end, tail = l.obtain(small)
    l.exists(If(end < 0, IntVal(0), end))
    j = l.fix()
    l.intro()
    l.specialize(steps, j - 1)
    l.specialize(tail, j)
    l.auto(by=[real.abs.defn(inv[j])])


@Theorem(
    ForAll(
        a,
        is_bounded_nonneg(a),
        Exists([F, s], And(is_subseq_index(F), has_lim(dommap(F, a), s))),
    )
)
def bolzano_weierstrass(l):
    """Every bounded real sequence has a convergent subsequence."""
    a = l.fix()
    bounded = l.intro()
    s, cluster = l.obtain(l.specialize(_exists_cluster, a, bounded))
    idx, converges = l.obtain(l.specialize(_exists_subseq_of_cluster, a, s, cluster))
    l.exists(idx, s)
    l.auto()


@Theorem(ForAll([a, F, s], is_subseq_index(F), has_lim(a, s), has_lim(dommap(F, a), s)))
def has_lim_subseq(l):
    """Every subsequence of a convergent sequence has the same limit."""
    a, idx, s = l.fixes()
    l.unfold(has_lim)
    _, tends = l.intros()
    l.unfold(dommap)
    eps = l.fix()
    positive = l.intro()
    N, close = l.obtain(l.specialize(tends, eps, positive))
    l.exists(If(N < 0, IntVal(0), N))
    j = l.fix()
    l.intro()
    l.have(idx[j] >= j, by=[le_subseq_index(idx, j)])
    l.specialize(close, idx[j])
    l.auto()
