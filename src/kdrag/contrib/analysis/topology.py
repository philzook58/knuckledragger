"""The sequence characterization of closed subsets of the real line."""

from kdrag import Theorem
from kdrag.smt import And, Exists, ForAll, If, IntVal, Lambda, Not, RealVal
import kdrag.theories.real as real
from kdrag.theories.real import rset
from kdrag.theories.real.rseq import (
    a,
    eventually,
    eventually_mono,
    eventually_near,
    has_lim,
    has_lim_inv,
    n,
    x,
    y,
    eps,
    near,
    shift,
)

from ._choice import exists_seq_of_forall_exists
from .rseq import has_lim_shift

A = real.A


@Theorem(
    ForAll(
        [A, a, x, eps],
        real.ball(x, eps) <= A,
        has_lim(a, x),
        eps > 0,
        eventually(Lambda(n, A[a[n]])),
    )
)
def _eventually_mem_of_ball_subset(l):
    A, a, x, radius = l.fixes()
    l.intros()
    close = near(a, x, radius)
    inside = Lambda(n, A[a[n]])
    l.have(eventually(close), by=[eventually_near(a, x, radius)])
    l.have(ForAll(n, close[n], inside[n]))
    j = l.fix()
    l.intro()
    l.have(
        real.ball(x, radius)[a[j]],
        by=[real.ball.defn(x, radius), real.abs.defn(a[j] - x)],
    )
    l.auto()
    l.auto(by=[eventually_mono(close, inside)])


@Theorem(
    ForAll(
        [A, a, x],
        real.is_open(A),
        A[x],
        has_lim(a, x),
        eventually(Lambda(n, A[a[n]])),
    )
)
def eventually_mem_of_is_open(l):
    """A sequence converging to a point of an open set eventually lies in it."""
    A, a, x = l.fixes()
    _, member, _ = l.intros()
    opened = l.have(real.is_open.defn(A).thm.arg(1), by=[real.is_open.defn(A)])
    radius, witness = l.obtain(l.specialize(opened, x, member))
    l.andE(witness)
    l.auto(by=[_eventually_mem_of_ball_subset(A, a, x, radius)])


@Theorem(
    ForAll(
        [A, a, x],
        real.is_closed(A),
        has_lim(a, x),
        eventually(Lambda(n, A[a[n]])),
        A[x],
    )
)
def mem_of_has_lim_of_eventually_mem(l):
    """A closed set contains the limit of a sequence eventually in the set."""
    A, a, x = l.fixes()
    l.unfold(eventually)
    l.intros()
    l.contra()
    inside = Lambda(n, A[a[n]])
    outside = Lambda(n, (~A)[a[n]])
    l.have(
        eventually(outside),
        by=[real.is_closed.defn(A), eventually_mem_of_is_open(~A, a, x)],
    )
    tail = l.have(eventually.defn(outside).thm.arg(1), by=[eventually.defn(outside)])
    N, avoids = l.obtain(tail)
    member_tail = l.have(eventually.defn(inside).thm.arg(1), by=[])
    M, belongs = l.obtain(member_tail)
    j = If(N < M, M, N) + 1
    l.specialize(avoids, j)
    l.specialize(belongs, j)
    l.auto()


@Theorem(
    ForAll(
        [A, x, eps],
        Not(real.interior_point(~A, x)),
        eps > 0,
        Exists(y, A[y], real.abs(y - x) < eps),
    )
)
def _exists_mem_near_of_not_interior_compl(l):
    A, x, eps = l.fixes()
    l.intros()
    l.contra()
    l.have(real.interior_point(~A, x))
    l.exists(eps)
    l.split()
    l.auto()
    l.auto(by=[real.ball.defn(x, eps), real.abs.defn])


@Theorem(
    ForAll(
        [a, x],
        ForAll(n, n >= 0, real.abs(a[n] - x) < RealVal(1) / (n + 1)),
        has_lim(a, x),
    )
)
def _has_lim_of_error_lt_inv_succ(l):
    a, x = l.fixes()
    error = l.intro()
    inv = Lambda(n, RealVal(1) / n)
    shifted = shift(inv, -1)
    l.have(has_lim(shifted, 0), by=[has_lim_inv, has_lim_shift(inv, 0, -1)])
    l.unfold(has_lim)
    eps = l.fix()
    l.intro()
    close = near(shifted, RealVal(0), eps)
    l.have(eventually(close), by=[eventually_near(shifted, RealVal(0), eps)])
    inverse_tail = l.have(
        eventually.defn(close).thm.arg(1), by=[eventually.defn(close)]
    )
    cutoff, small = l.obtain(inverse_tail)
    l.exists(If(cutoff < 0, IntVal(0), cutoff))
    j = l.fix()
    l.intro()
    l.specialize(small, j)
    l.specialize(error, j)
    l.auto(by=[shift.defn(inv, -1), real.abs.defn(RealVal(1) / (j + 1))])


@Theorem(
    ForAll(
        A,
        ForAll([a, x], ForAll(n, n >= 0, A[a[n]]), has_lim(a, x), A[x]),
        real.is_closed(A),
    )
)
def is_closed_of_seq_limits(l):
    """A set containing the limits of its convergent sequences is closed."""
    A = l.fix()
    retains_limits = l.intro()
    l.unfold(real.is_closed)
    l.unfold(real.is_open)
    x = l.fix()
    l.intro()
    l.contra()

    # A point outside the set with no disjoint neighborhood is a sequence limit.
    near = Lambda([n, y], And(A[y], real.abs(y - x) < RealVal(1) / (n + 1)))
    l.have(ForAll(n, n >= 0, Exists(y, near[n, y])))
    j = l.fix()
    l.intro()
    radius = RealVal(1) / (j + 1)
    l.have(radius > 0, by=[])
    l.auto(by=[_exists_mem_near_of_not_interior_compl(A, x, radius)])
    choice = l.have(
        Exists(a, ForAll(n, n >= 0, near[n, a[n]])),
        by=[exists_seq_of_forall_exists(near)],
    )
    seq, points = l.obtain(choice)
    l.have(ForAll(n, n >= 0, A[seq[n]]), by=[])
    l.have(ForAll(n, n >= 0, real.abs(seq[n] - x) < RealVal(1) / (n + 1)), by=[])
    l.clear(points)
    l.have(has_lim(seq, x), by=[_has_lim_of_error_lt_inv_succ(seq, x)])
    l.specialize(retains_limits, seq, x)
    l.auto()


@Theorem(ForAll([x, y], real.is_closed(real.icc(x, y))))
def is_closed_icc(l):
    """The complement of a closed interval is open."""
    lo, hi = l.fixes()
    l.unfold(real.is_closed)
    l.unfold(real.is_open)
    p = l.fix()
    l.intro()
    radius = If(p < lo, lo - p, p - hi)
    l.exists(radius)
    l.split()
    l.auto(by=[real.icc.defn(lo, hi)])
    l.auto(by=[real.ball.defn(p, radius), real.icc.defn(lo, hi)])


@Theorem(ForAll([A, x], real.is_closed(A), real.closure(A)[x], A[x]))
def mem_of_mem_closure(l):
    """A closed set contains its closure."""
    A, x = l.fixes()
    l.unfold(real.closure)
    l.beta()
    _, approximants = l.intros()
    l.contra()
    l.have(real.is_open(~A), by=[real.is_closed.defn(A)])
    opened = l.have(real.is_open.defn(~A).thm.arg(1), by=[real.is_open.defn(~A)])
    outside = l.have((~A)[x], by=[])
    radius, witness = l.obtain(l.specialize(opened, x, outside))
    positive, _ = l.andE(witness)
    l.obtain(l.specialize(approximants, radius, positive))
    l.auto()


@Theorem(ForAll([A, x], real.is_closed(A), rset.is_lub(A, x), A[x]))
def mem_of_is_lub_of_is_closed(l):
    """A real supremum of a closed set belongs to the set."""
    A, x = l.fixes()
    l.intros()
    l.have(real.closure(A)[x])
    l.unfold(real.closure)
    l.beta()
    eps = l.fix()
    l.intro()
    # Lowering the supremum by eps gives a point within eps of it.
    l.have(Not(rset.is_ub(A, x - eps)), by=[rset.le_of_is_lub_of_is_ub(A, x, x - eps)])
    near = l.have(Exists(y, A[y], x - eps < y), by=[rset.is_ub.defn(A, x - eps)])
    point, _ = l.obtain(near)
    l.have(
        point <= x,
        by=[rset.is_ub_of_is_lub(A, x), rset.le_of_mem_of_is_ub(A, point, x)],
    )
    l.exists(point)
    l.auto(by=[real.ball.defn(x, eps)])
    l.auto(by=[mem_of_mem_closure(A, x)])


@Theorem(ForAll([A, x], real.is_closed(A), rset.is_glb(A, x), A[x]))
def mem_of_is_glb_of_is_closed(l):
    """A real infimum of a closed set belongs to the set."""
    A, x = l.fixes()
    l.intros()
    l.have(real.closure(A)[x])
    l.unfold(real.closure)
    l.beta()
    eps = l.fix()
    l.intro()
    # Raising the infimum by eps gives a point within eps of it.
    l.have(Not(rset.is_lb(A, x + eps)), by=[rset.is_glb.defn(A, x)])
    near = l.have(Exists(y, A[y], y < x + eps), by=[rset.is_lb.defn(A, x + eps)])
    point, _ = l.obtain(near)
    l.have(x <= point, by=[rset.is_glb.defn(A, x), rset.is_lb.defn(A, x)])
    l.exists(point)
    l.auto(by=[real.ball.defn(x, eps)])
    l.auto(by=[mem_of_mem_closure(A, x)])
