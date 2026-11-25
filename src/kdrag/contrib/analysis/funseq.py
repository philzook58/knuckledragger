"""Uniform convergence of real-valued function sequences."""

from kdrag import Theorem, define
from kdrag.smt import Array, Const, Eq, Exists, ForAll, IntSort, Ints, Lambda, Reals
import kdrag.theories.real as real
from kdrag.theories.real import rseq

from .cauchy import is_cauchy_iff_exists_has_lim
from .rseq import abs_sub_le_of_has_lim

F = Array("F", IntSort(), real.RFun)
f = Const("f", real.RFun)
A = real.A
n, m, N = Ints("n m N")
x, eps = Reals("x eps")

# Abbott 6.2.3. The cutoff in eventually is shared by every x in A.
has_uniform_lim_on = define(
    "analysis.has_uniform_lim_on",
    [F, f, A],
    ForAll(
        eps,
        eps > 0,
        rseq.eventually(Lambda(n, ForAll(x, A[x], real.abs(F[n][x] - f[x]) < eps))),
    ),
)

uniform_cauchy_on = define(
    "analysis.uniform_cauchy_on",
    [F, A],
    ForAll(
        eps,
        eps > 0,
        Exists(
            N,
            ForAll(
                [n, m], n > N, m > N, ForAll(x, A[x], real.abs(F[n][x] - F[m][x]) < eps)
            ),
        ),
    ),
)


@Theorem(ForAll([F, f, A], has_uniform_lim_on(F, f, A), uniform_cauchy_on(F, A)))
def uniform_cauchy_on_of_has_uniform_lim_on(l):
    """Use the same cutoff for both terms, each within eps/2 of the limit."""
    F, f, A = l.fixes()
    l.unfold(has_uniform_lim_on, uniform_cauchy_on)
    l.unfold(rseq.eventually)
    l.beta()
    converges = l.intro()
    eps = l.fix()
    l.intro()
    half = l.have(eps / 2 > 0, by=[])
    cutoff, close = l.obtain(l.specialize(converges, eps / 2, half))
    l.exists(cutoff)
    n, m = l.fixes()
    late_n, late_m = l.intros()
    near_n = l.specialize(close, n, late_n, keep=True)
    near_m = l.specialize(close, m, late_m)
    x = l.fix()
    member = l.intro()
    l.specialize(near_n, x, member)
    l.specialize(near_m, x, member)
    l.auto(by=[real.abs_triangle(F[n][x], F[m][x], f[x]), real.abs_neg(F[m][x] - f[x])])


@Theorem(
    ForAll([F, A], Eq(uniform_cauchy_on(F, A), Exists(f, has_uniform_lim_on(F, f, A))))
)
def uniform_cauchy_on_iff_exists_has_uniform_lim_on(l):
    """Abbott 6.2.5. Uniformly Cauchy function sequences have a uniform limit."""
    F, A = l.fixes()
    l.split()
    l.unfold(uniform_cauchy_on)
    tails = l.intro()

    # Each x in A determines a Cauchy sequence of real numbers.
    limit = Lambda(x, rseq.lim(Lambda(n, F[n][x])))
    pointwise = l.have(ForAll(x, A[x], rseq.has_lim(Lambda(n, F[n][x]), limit[x])))
    point = l.fix()
    member = l.intro()
    values = Lambda(n, F[n][point])
    l.have(rseq.is_cauchy(values))
    l.unfold(rseq.is_cauchy)
    l.beta()
    eps = l.fix()
    positive = l.intro()
    cutoff, close = l.obtain(l.specialize(tails, eps, positive))
    l.exists(cutoff)
    left, right = l.fixes()
    late_n, late_m = l.intros()
    at_point = l.specialize(close, left, right, late_n, late_m)
    l.specialize(at_point, point, member)
    l.assumption()
    l.beta()
    l.auto(
        by=[
            is_cauchy_iff_exists_has_lim(values),
            rseq.is_conv.defn(values),
            rseq.lim_defn.forall([rseq.A])(values),
        ]
    )

    # For n past the common cutoff, send m to infinity in the tail bound.
    l.exists(limit)
    l.unfold(has_uniform_lim_on)
    l.unfold(rseq.eventually)
    l.beta()
    eps = l.fix()
    l.intro()
    half = l.have(eps / 2 > 0, by=[])
    cutoff, close = l.obtain(l.specialize(tails, eps / 2, half))
    l.exists(cutoff)
    index = l.fix()
    l.intro()
    point = l.fix()
    member = l.intro()
    l.specialize(pointwise, point, member)
    values = Lambda(n, F[n][point])
    l.have(
        ForAll(m, m >= cutoff + 1, real.abs(F[m][point] - F[index][point]) <= eps / 2)
    )
    other = l.fix()
    l.intro()
    l.specialize(close, other, index)
    l.auto()
    l.auto(
        by=[
            abs_sub_le_of_has_lim(
                values, limit[point], F[index][point], eps / 2, cutoff + 1
            ),
            real.abs_neg(limit[point] - F[index][point]),
        ]
    )

    f, _ = l.obtain(l.intro())
    l.auto(by=[uniform_cauchy_on_of_has_uniform_lim_on(F, f, A)])
