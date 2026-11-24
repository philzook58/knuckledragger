"""Sequential compactness of real sets and the nested compact set property."""

from kdrag import Theorem, define
from kdrag.smt import (
    And,
    Eq,
    Exists,
    ForAll,
    If,
    IntVal,
    Lambda,
    ToInt,
    ToReal,
)
import kdrag.theories.real as real
from kdrag.theories.real.rseq import (
    F,
    a,
    dommap,
    eventually,
    has_lim,
    lim_unique,
    n,
    x,
    y,
)
from kdrag.theories.real.rset import An, M, nested, nested_subset

from ._choice import exists_seq_of_forall_exists
from .cauchy import is_bounded_nonneg_of_is_cauchy, is_cauchy_of_has_lim
from .subsequence import (
    bolzano_weierstrass,
    has_lim_subseq,
    is_bounded_nonneg,
    is_subseq_index,
    le_subseq_index,
)
from .topology import (
    is_closed_icc,
    is_closed_of_seq_limits,
    mem_of_has_lim_of_eventually_mem,
)

A = real.A

is_compact = define(
    "analysis.is_compact",
    A,
    ForAll(
        a,
        ForAll(n, n >= 0, A[a[n]]),
        Exists([F, x], And(is_subseq_index(F), has_lim(dommap(F, a), x), A[x])),
    ),
)
is_bounded = define(
    "analysis.is_bounded",
    A,
    Exists(M, M > 0, ForAll(x, A[x], real.abs(x) <= M)),
)


@Theorem(
    ForAll(
        [A, a],
        is_compact(A),
        ForAll(n, n >= 0, A[a[n]]),
        Exists([F, x], And(is_subseq_index(F), has_lim(dommap(F, a), x), A[x])),
    )
)
def exists_subseq_of_is_compact(l):
    A, a = l.fixes()
    l.unfold(is_compact)
    compact, in_set = l.intros()
    l.specialize(compact, a, in_set)
    l.auto()


@Theorem(ForAll(A, is_compact(A), real.is_closed(A)))
def is_closed_of_is_compact(l):
    A = l.fix()
    compact = l.intro()
    l.have(ForAll([a, x], ForAll(n, n >= 0, A[a[n]]), has_lim(a, x), A[x]))
    seq, point = l.fixes()
    in_set, _ = l.intros()
    (idx, limit), witness = l.obtain(
        l.specialize(exists_subseq_of_is_compact, A, seq, compact, in_set)
    )
    l.andE(witness)
    subseq = dommap(idx, seq)
    l.have(has_lim(subseq, point), by=[has_lim_subseq(seq, idx, point)])
    l.auto(by=[lim_unique(subseq, limit, point)])
    l.auto(by=[is_closed_of_seq_limits(A)])


@Theorem(ForAll(A, is_compact(A), is_bounded(A)))
def is_bounded_of_is_compact(l):
    A = l.fix()
    compact = l.intro()
    l.unfold(is_bounded)
    l.contra()
    # If the set is unbounded, choose a term with magnitude above n + 1.
    far = Lambda([n, x], And(A[x], real.abs(x) > ToReal(n) + 1))
    l.have(ForAll(n, n >= 0, Exists(x, far[n, x])))
    j = l.fix()
    l.intro()
    l.beta()
    l.contra()
    l.have(Exists(M, M > 0, ForAll(x, A[x], real.abs(x) <= M)))
    l.exists(ToReal(j) + 1)
    l.split()
    l.auto()
    l.fix()
    l.intro()
    l.auto()
    l.auto()
    chosen = l.have(
        Exists(a, ForAll(n, n >= 0, far[n, a[n]])),
        by=[exists_seq_of_forall_exists(far)],
    )
    seq, large = l.obtain(chosen)
    in_set = l.have(ForAll(n, n >= 0, A[seq[n]]), by=[])
    (idx, limit), witness = l.obtain(
        l.specialize(exists_subseq_of_is_compact, A, seq, compact, in_set)
    )
    l.andE(witness)
    subseq = dommap(idx, seq)
    l.have(
        is_bounded_nonneg(subseq),
        by=[
            is_cauchy_of_has_lim(subseq, limit),
            is_bounded_nonneg_of_is_cauchy(subseq),
        ],
    )
    bounded = l.have(
        Exists(M, ForAll(n, n >= 0, real.abs(subseq[n]) <= M)),
        by=[is_bounded_nonneg.defn(subseq)],
    )
    B, bound = l.obtain(bounded)
    j = If(B < 0, IntVal(0), ToInt(B) + 1)
    l.have(idx[j] >= j, by=[le_subseq_index(idx, j)])
    l.specialize(large, idx[j])
    l.specialize(bound, j)
    l.auto(by=[dommap.defn(idx, seq)])


@Theorem(ForAll(A, real.is_closed(A), is_bounded(A), is_compact(A)))
def is_compact_of_is_closed_of_is_bounded(l):
    A = l.fix()
    l.unfold(is_bounded, is_compact)
    _, bounded = l.intros()
    B, bound = l.obtain(bounded)
    _, bounds = l.andE(bound)
    seq = l.fix()
    in_set = l.intro()
    bounded_seq = l.have(is_bounded_nonneg(seq))
    l.unfold(is_bounded_nonneg)
    l.exists(B)
    j = l.fix()
    l.intro()
    l.specialize(in_set, j)
    l.specialize(bounds, seq[j])
    l.auto()

    (idx, limit), witness = l.obtain(
        l.specialize(bolzano_weierstrass, seq, bounded_seq)
    )
    l.andE(witness)
    subseq = dommap(idx, seq)
    l.have(eventually(Lambda(n, A[subseq[n]])))
    l.unfold(eventually)
    l.exists(IntVal(0))
    j = l.fix()
    l.intro()
    l.have(idx[j] >= j, by=[le_subseq_index(idx, j)])
    l.specialize(in_set, idx[j])
    l.auto(by=[dommap.defn(idx, seq)])
    l.exists(idx, limit)
    l.auto(by=[mem_of_has_lim_of_eventually_mem(A, subseq, limit)])


@Theorem(ForAll(A, Eq(is_compact(A), And(real.is_closed(A), is_bounded(A)))))
def is_compact_iff_is_closed_and_bounded(l):
    """Abbott 3.3.4."""
    A = l.fix()
    l.auto(
        by=[
            is_closed_of_is_compact(A),
            is_bounded_of_is_compact(A),
            is_compact_of_is_closed_of_is_bounded(A),
        ]
    )


@Theorem(ForAll([x, y], is_compact(real.icc(x, y))))
def is_compact_icc(l):
    """Closed intervals are compact (Abbott 3.3.2)."""
    lo, hi = l.fixes()
    interval = real.icc(lo, hi)
    l.have(is_bounded(interval))
    l.unfold(is_bounded)
    l.exists(real.abs(lo) + real.abs(hi) + 1)
    l.split()
    l.auto(by=[real.abs_pos(lo), real.abs_pos(hi)])
    point = l.fix()
    l.intro()
    l.auto(
        by=[
            real.abs.defn(point),
            real.abs.defn(lo),
            real.abs.defn(hi),
            real.icc.defn(lo, hi),
        ]
    )
    l.auto(by=[is_closed_icc(lo, hi), is_compact_of_is_closed_of_is_bounded(interval)])


@Theorem(
    ForAll(
        An,
        nested(An),
        ForAll(n, n >= 0, is_compact(An[n])),
        ForAll(n, n >= 0, Exists(x, An[n][x])),
        Exists(x, real.iinter(An)[x]),
    )
)
def nonempty_iinter_of_nested_compact(l):
    """Nested nonempty compact sets have a common point (Abbott 3.3.5)."""
    sets = l.fix()
    _, compacts, _ = l.intros()
    point_in_set = Lambda([n, x], sets[n][x])
    chosen = l.have(
        Exists(a, ForAll(n, n >= 0, point_in_set[n, a[n]])),
        by=[exists_seq_of_forall_exists(point_in_set)],
    )
    seq, belongs = l.obtain(chosen)
    in_first = l.have(ForAll(n, n >= 0, sets[0][seq[n]]))
    j = l.fix()
    l.intro()
    l.specialize(belongs, j)
    l.auto(by=[nested_subset(sets, 0, j)])

    first = l.have(is_compact(sets[0]), by=[])
    (idx, limit), witness = l.obtain(
        l.specialize(exists_subseq_of_is_compact, sets[0], seq, first, in_first)
    )
    l.andE(witness)
    l.exists(limit)
    l.unfold(real.iinter)
    l.beta()
    m = l.fix()
    l.intro()
    l.specialize(compacts, m)
    subseq = dommap(idx, seq)
    # The subsequence eventually lies in each fixed set.
    l.have(eventually(Lambda(n, sets[m][subseq[n]])))
    l.unfold(eventually)
    l.exists(m)
    j = l.fix()
    l.intro()
    l.have(idx[j] >= j, by=[le_subseq_index(idx, j)])
    l.specialize(belongs, idx[j])
    l.auto(by=[nested_subset(sets, m, idx[j]), dommap.defn(idx, seq)])
    l.auto(
        by=[
            is_closed_of_is_compact(sets[m]),
            mem_of_has_lim_of_eventually_mem(sets[m], subseq, limit),
        ]
    )
