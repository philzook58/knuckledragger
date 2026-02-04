# %%
import kdrag as kd
import kdrag.smt as smt

import kdrag.theories.int as int_
import kdrag.theories.real as real


RSeq = real.RSeq
R = real.R

a, b, c = smt.Consts("a b c", RSeq)
A, B, C = kd.FreshVars("A B C", RSeq)
i, j, k, n, m, N = smt.Ints("i j k n m N")
x, y, z, eps, delta, M = smt.Reals("x y z eps delta M")

zero = kd.define("zero", [], smt.K(smt.IntSort(), smt.RealVal(0)))
const = kd.define("const", [x], smt.Lambda([i], x))
id_ = kd.define("id", [], smt.Lambda([i], smt.ToReal(i)))
assert isinstance(id_, smt.ExprRef)  # for typechecker

geom = kd.define("geom", [x], smt.Lambda([i], real.pownat(x, i)))

S = smt.Array("S", smt.IntSort(), smt.BoolSort())
ind = kd.define(
    "ind", [S], smt.Lambda([i], smt.If(S[i], smt.RealVal(1), smt.RealVal(0)))
)  # indicator sequence / iverson bracket

F = smt.Array("F", smt.IntSort(), smt.IntSort())
dommap = kd.define("dommap", [F, a], smt.Lambda([i], a[F[i]]))

# Domain operations
shift = kd.define("shift", [a, n], smt.Lambda([i], a[i - n]))
delay = kd.define("delay", [a], shift(a, 1))
rev = kd.define("rev", [a], smt.Lambda([i], a[-i]))
dilate = kd.define("dilate", [a, n], smt.Lambda([i], a[i / n]))
decimate = kd.define("decimate", [a, n], smt.Lambda([i], a[i * n]))


mask = smt.Array("mask", smt.IntSort(), smt.BoolSort())
where = kd.define("where", [mask, a, b], smt.Lambda([i], smt.If(mask[i], a[i], b[i])))
krondelta = kd.define(
    "krondelta", [n], smt.Lambda([i], smt.If(i == n, smt.RealVal(1), smt.RealVal(0)))
)
pos = kd.define("pos", [a], smt.Lambda([i], smt.If(i >= 0, a[i], smt.RealVal(0))))
# arange = kd.define("arange", [n], smt.Lambda([i], smt.ToReal(i) * smt.ToReal(n >= i)))

# numpy names
zeros = zero
full = const
roll = shift

diff = kd.define("diff", [a], smt.Lambda([i], a[i + 1] - a[i]))


add = kd.notation.add.define([a, b], smt.Lambda([i], a[i] + b[i]))
# add = kd.define("add", [a, b], smt.Map(real.add, a, b))
kd.notation.add.register(RSeq, add)
add_comm = kd.prove(
    A + B == B + A, by=[add.defn(B, A), add.defn(A, B), real.add_comm]
).forall([A, B])
add_assoc = kd.prove(
    (A + B) + C == A + (B + C),
    unfold=1,
    by=[real.add_assoc],
).forall([A, B, C])
# kd.Lemma(diff(cumsum(A)) == A)


sub = kd.notation.sub.define([a, b], smt.Lambda([i], a[i] - b[i]))
mul = kd.notation.mul.define([a, b], smt.Lambda([i], a[i] * b[i]))
div = kd.notation.div.define([a, b], smt.Lambda([i], a[i] / b[i]))
neg = kd.notation.neg.define([a], smt.Lambda([i], -a[i]))

smul = kd.define("smul", [x, a], smt.Lambda([n], x * a[n]))


rev_rev = kd.prove(rev(rev(A)) == A, by=[rev.defn]).forall([A])
shift_shit = kd.prove(
    smt.ForAll([n, m, a], shift(shift(a, n), m) == shift(a, n + m)), by=[shift.defn]
)
rev_shift = kd.prove(
    smt.ForAll([n, a], rev(shift(a, n)) == shift(rev(a), -n)), by=[shift.defn, rev.defn]
)
rev_zero = kd.prove(rev(zero) == zero, by=[rev.defn, zero.defn])
rev_const = kd.prove(
    smt.ForAll([x], rev(const(x)) == const(x)), by=[rev.defn, const.defn]
)
rev_id = kd.prove(rev(id_) == -id_, by=[rev.defn, id_.defn, neg.defn])


def test():
    """
    >>> True
    True
    """


cumsum = smt.Function("cumsum", RSeq, RSeq)
cumsum = kd.define(
    "cumsum",
    [a],
    smt.Lambda(
        [i],
        smt.If(  # Maybe this is a badly shifted definition
            i == 0,
            a[0],
            smt.If(i > 0, cumsum(a)[i - 1] + a[i], -cumsum(a)[i + 1] - a[i + 1]),
        ),
    ),
)


@kd.Theorem("forall (n : Int), cumsum zero n = 0")
def cumsum_zero(l):
    n = l.fix()
    l.unfold(zero)
    l.induct(n)

    # n < 0
    l.fix()
    l.intros()
    l.unfold(cumsum)
    l.auto()

    # n == 0
    l.unfold(cumsum)
    l.auto()

    # n > 0
    l.fix()
    l.intros()
    l.unfold(cumsum)
    l.auto()


@kd.Theorem(
    "forall (x : Real) (n : Int), n >= 0 -> cumsum (const x) n = (n + 1) * x"
)  # TODO: fix for n < 0. Wrong definition?
def cumsum_const(l):
    x, n = l.fixes()
    l.unfold(const)
    l.induct(n)

    # n < 0
    # l.fix()
    # l.intros()
    # l.unfold(cumsum)
    # l.simp()
    l.auto()

    # n == 0
    l.unfold(cumsum)
    l.auto()

    # n > 0
    n = l.fix()
    l.intros()
    l.intros()
    l.unfold(cumsum)
    # l.boolsimp() # boolsimp is not working well
    # l.simp()
    # l.have((n == -1) == False, by=[])
    # l.rw(-1)
    # l.have((n <= -1) == False, by=[])
    # l.rw(-1)
    l.auto()


# TODO: cumsum id_ = n * (n + 1) / 2
# cumsum pownat = 1 - x^(n + 1) / (1 - x)
# cumsum_diff - the fundamental theorem of calculus for sequences

"""

# TODO: cumsum_comm = cumsum(lambda x, cumsum(lammbda y, a[x,y]) ) ???


# TODO: unstable
@kd.Theorem(
    "forall (a : RSeq) (x : Real) (n : Int), cumsum (smul x a) n = smul x (cumsum a) n"
)
def cumsum_smul(l):
    a, x, n = l.fixes()
    l.induct(n)

    # n < 0
    # TODO: These induction cases look disgusting with too many lambdas.
    l.fix()
    l.simp()
    l.intros()
    l.unfold(cumsum, smul)
    l.simp()
    l.auto(by=[smul.defn, cumsum.defn])

    # n == 0
    l.auto(by=[smul.defn, cumsum.defn])

    # n > 0
    l.fix()
    l.simp()
    l.unfold(cumsum, smul)
    l.simp()
    l.unfold(cumsum, smul)
    l.simp()
    l.auto(by=[smul.defn, cumsum.defn])
"""


@kd.Theorem(
    "forall (a b : RSeq) (m : Int), (forall (n : Int), n >= 0 -> a n <= b n) -> m >= 0 -> cumsum a m <= cumsum b m"
)
def cumsul_mono(l):
    a, b, m = l.fixes()
    l.intros()
    l.induct(m)
    _n = l.fix()
    l.auto()

    # n == 0
    l.auto(by=[cumsum.defn])

    # n > 0
    _n = l.fix()
    l.intros()
    l.simp()
    l.intros()
    l.unfold(cumsum)
    l.auto(by=[cumsum.defn])


@kd.Theorem("forall (a b : RSeq) (n : Int), cumsum (a + b) n = cumsum a n + cumsum b n")
def cumsul_add(l):
    a, x, n = l.fixes()
    l.induct(n)

    # n < 0
    # TODO: These induction cases look disgusting with too many lambdas.
    l.fix()
    l.simp()
    l.intros()
    l.unfold(cumsum, add)
    l.simp()
    l.auto(by=[add.defn, cumsum.defn])

    # n == 0
    l.auto(by=[add.defn, cumsum.defn])

    # n > 0
    l.fix()
    l.simp()
    l.unfold(cumsum, add)
    l.simp()
    l.unfold(cumsum, add)
    l.simp()
    l.auto(by=[add.defn, cumsum.defn])


max = smt.Function("max", RSeq, RSeq)
max = kd.define(
    "max",
    [a],
    smt.Lambda(
        [i],
        smt.If(
            i == 0,
            a[0],
            smt.If(
                i > 0,
                real.max(max(a)[i - 1], a[i]),
                real.max(max(a)[i + 1], a[i]),
            ),
        ),
    ),
)


@kd.Theorem(smt.ForAll([a, i], max(a)[i] >= a[i]))
def max_ge_self(l):
    a, i = l.fixes()
    l.unfold(max)
    l.auto(by=[real.max_ge_2])


@kd.Theorem(
    kd.QForAll(
        [a, n],
        n >= 0,
        kd.QForAll([i], i >= 0, i <= n, a[i] <= max(a)[n]),
    )
)
def max_prefix_bound(l):
    a, n = l.fixes()
    # l.intros()
    l.induct(n)  # Some weird stuff happened here
    l.auto()  # n < 0
    l.auto(by=[max.defn])  # n == 0. Kind of weird that we lose the equality...
    n = l.fix()
    l.intros()
    l.split(at=0)
    l.simp(at=-1)
    i = smt.Int("i")
    l.have(smt.ForAll([i], i >= 0, i <= n, a[i] <= max(a)[n]), by=[])
    l.intros()
    i = l.fix()
    l.intros()
    l.specialize(2, i)
    l.unfold(max)
    l.simp()
    l.unfold(real.max)
    l.auto()


max_bound = kd.prove(
    kd.QForAll([a, n, i], n >= 0, i >= 0, i <= n, a[i] <= max(a)[n]),
    by=[max_prefix_bound],
)


@kd.Theorem(
    kd.QForAll(
        [a, n],
        n <= 0,
        kd.QForAll([i], n <= i, i <= 0, a[i] <= max(a)[n]),
    )
)
def max_suffix_bound(l):
    a, n = l.fixes()
    l.induct(n)
    # step: n <= 0 -> n - 1
    n = l.fix()
    l.intros()
    l.intros()
    i = l.fix()
    l.intros()
    l.split(at=0)
    l.cases(i == n - 1)
    l.have(i == n - 1, by=[])
    l.unfold(max)
    l.simp()
    l.unfold(real.max)
    l.auto(by=[real.max_ge_2])
    l.have(i != n - 1, by=[])
    l.have(n <= i, by=[])
    j = smt.Int("j")
    l.have(kd.QForAll([j], n <= j, j <= 0, a[j] <= max(a)[n]), by=[])
    l.specialize(-1, i)
    l.have(a[i] <= max(a)[n], by=[])
    l.unfold(max)
    l.simp()
    l.unfold(real.max)
    l.auto(by=[real.max_ge])
    # base: n == 0
    l.auto(by=[max.defn])
    # step: n >= 0 -> n + 1
    l.auto()


Sum = smt.Function("Sum", RSeq, smt.IntSort(), smt.IntSort(), R)
finsum = kd.define("finsum", [a, n], cumsum(a)[n])


sin = kd.define("sin", [a], smt.Map(real.sin, a))
cos = kd.define("cos", [a], smt.Map(real.cos, a))

abs = kd.define("abs", [a], smt.Map(real.abs, a))
abs_ext = kd.prove(smt.ForAll([a, n], abs(a)[n] == real.abs(a[n])), by=[abs.defn])
abs_ge_0 = kd.prove(
    kd.QForAll([a, n], abs(a)[n] >= 0),
    by=[abs_ext, real.abs_pos],
)


@kd.Theorem(
    kd.QForAll(
        [a, N],
        N >= 0,
        kd.QForAll([n], n >= 0, n <= N, abs(a)[n] <= finsum(abs(a), N)),
    )
)
def abs_le_finsum_abs(l):
    a, N = l.fixes()

    l.induct(N, using=int_.induct_nat)
    # base case: N = 0
    l.intros()
    n = l.fix()
    l.intros()
    l.split(at=-1)
    l.have(n == 0, by=[])
    l.rw(-1)
    l.unfold(finsum)
    l.unfold(cumsum)
    l.simp()
    l.auto()

    # step: N >= 0, IH -> N + 1
    N = l.fix()
    l.intros()
    l.intros()

    n = l.fix()
    l.intros()
    l.split(at=0)

    # Case split: n <= N or n = N + 1
    l.cases(n <= N)

    # n <= N: use IH and monotonicity of finsum
    l.have(abs(a)[n] <= finsum(abs(a), N), by=[])
    l.have(N + 1 > 0, by=[])
    l.have(
        finsum(abs(a), N + 1) == finsum(abs(a), N) + abs(a)[N + 1],
        by=[finsum.defn, cumsum.defn],
    )
    l.have(abs(a)[N + 1] >= 0, by=[abs_ge_0])
    l.have(finsum(abs(a), N) <= finsum(abs(a), N + 1), by=[])
    l.auto()

    # n > N: then n = N + 1
    l.have(n == N + 1, by=[])
    l.rw(-1)
    l.have(N + 1 > 0, by=[])
    l.have(
        finsum(abs(a), N + 1) == finsum(abs(a), N) + abs(a)[N + 1],
        by=[finsum.defn, cumsum.defn],
    )
    l.have(abs(a)[N + 1] >= 0, by=[abs_ge_0])
    l.have(abs(a)[0] <= finsum(abs(a), N), by=[])
    l.have(abs(a)[0] >= 0, by=[abs_ge_0])
    l.have(finsum(abs(a), N + 1) >= abs(a)[N + 1], by=[])
    l.auto()


has_bound = kd.define("has_bound", [a, M], kd.QForAll([n], real.abs(a[n]) <= M))
is_bounded = kd.define("is_bounded", [a], smt.Exists([M], has_bound(a, M)))

is_monotone = kd.define("is_monotone", [a], kd.QForAll([n, m], n <= m, a[n] <= a[m]))
is_nonneg = kd.define("is_nonneg", [a], kd.QForAll([n], a[n] >= 0))

# https://en.wikipedia.org/wiki/Cauchy_sequence

mod = smt.Const("mod", smt.ArraySort(smt.RealSort(), smt.IntSort()))

is_cauchy = kd.define(
    "is_cauchy",
    [a],
    kd.QForAll(
        [eps],
        eps > 0,
        smt.Exists([N], kd.QForAll([m, k], m > N, k > N, real.abs(a[m] - a[k]) < eps)),
    ),
)
cauchy_mod = kd.define(
    "cauchy_mod",
    [a, mod],
    kd.QForAll(
        [eps],
        eps > 0,
        kd.QForAll([m, k], m > mod[eps], k > mod[eps], real.abs(a[m] - a[k]) < eps),
    ),
)
"""
is_convergent = kd.define(
    "is_convergent",
    [a],
    kd.QForAll(
        [eps],
        eps > 0,
        smt.Exists(
            [N], kd.QForAll([m], m > N, smt.Exists([x], real.abs(a[m] - x) < eps))
        ),
    ),
)
"""
# limit of sequence as n -> infinity
has_lim = kd.define(
    "has_lim",
    [a, y],
    kd.QForAll(
        [eps],
        eps > 0,
        kd.QExists([N], kd.QForAll([n], n > N, real.abs(a[n] - y) < eps)),
    ),
)

# convergent
is_conv = kd.define("is_conv", [a], smt.Exists([y], has_lim(a, y)))

# skolemize and define
(sk,), pf = kd.kernel.obtain(smt.Exists([y], has_lim(A, y)))
lim = kd.define("lim", [A], sk)
lim_defn = kd.prove(
    smt.Implies(is_conv(A), has_lim(A, lim(A))), by=[lim.defn, pf, is_conv.defn]
)


# kd.Lemma(has_lim(zero, 0)).unfold(has_lim).unfold(zero).unfold(real.abs)
lim_zero = kd.prove(has_lim(zero, 0), by=[has_lim.defn, zero.defn, real.abs.defn])
lim_const = kd.prove(has_lim(const(x), x), by=[has_lim.defn, const.defn, real.abs.defn])


@kd.Theorem(has_lim(smt.Lambda([n], smt.RealVal(1) / n), smt.RealVal(0)))
def has_lim_inv(l):
    l.unfold(has_lim)
    eps = l.fix()
    l.assumes(eps > 0)
    l.exists(smt.ToInt(1 / eps) + 1)
    n = l.fix()
    l.assumes(n > smt.ToInt(1 / eps) + 1)
    l.unfold(real.abs)
    l.auto()


@kd.Theorem("forall (a : RSeq) (x y : Real), has_lim a x -> has_lim a y -> x = y")
def lim_unique(l):
    a, x, y = l.fixes()
    l.intros()
    l.intros()
    l.contra()
    eps = real.abs(x - y) / 2
    l.unfold(has_lim, at=0)
    l.unfold(has_lim, at=1)
    hx = l.top_goal().ctx[0]
    hy = l.top_goal().ctx[1]
    l.specialize(hx, eps)
    l.specialize(hy, eps)
    l.have(real.abs(x - y) > 0, by=[real.abs_pos_iff])
    l.have(eps > 0, by=[])
    n1 = smt.Int("N")  # "N1" is problem for alpha rename
    n2 = smt.Int("N")  # "N2" is problem for alpha rename
    n = smt.Int("n")
    exists_x = kd.QExists(
        [n1],
        kd.QForAll([n], n > n1, real.abs(a[n] - x) < eps),
    )
    exists_y = kd.QExists(
        [n2],
        kd.QForAll([n], n > n2, real.abs(a[n] - y) < eps),
    )
    l.have(exists_x, by=[])  # unstable due to alpha rename?
    N1 = l.obtain(exists_x)
    l.have(exists_y, by=[])
    N2 = l.obtain(exists_y)
    N = smt.If(N1 > N2, N1, N2) + 1
    forall_x = kd.QForAll([n], n > N1, real.abs(a[n] - x) < eps)
    forall_y = kd.QForAll([n], n > N2, real.abs(a[n] - y) < eps)
    l.specialize(forall_x, N)
    l.specialize(forall_y, N)
    l.have(N > N1, by=[])
    l.have(N > N2, by=[])
    l.have(real.abs(a[N] - x) < eps, by=[])
    l.have(real.abs(a[N] - y) < eps, by=[])
    l.have(real.abs(x - a[N]) < eps, by=[real.abs_neg])
    l.have(
        real.abs(x - y) <= real.abs(x - a[N]) + real.abs(a[N] - y),
        by=[real.abs_triangle(x, y, a[N])],
    )
    l.have(
        real.abs(x - y) < eps + eps,
        by=[real.abs_triangle(x, y, a[N])],
    )
    l.have(eps + eps == real.abs(x - y), by=[])
    l.have(real.abs(x - y) < real.abs(x - y), by=[])
    l.auto()


has_sum = kd.define("has_sum", [a, y], has_lim(cumsum(a), y))
is_summable = kd.define("is_summable", [a], smt.Exists([y], has_sum(a, y)))


class Series:
    # https://www.cs.dartmouth.edu/~doug/powser.html
    powers = smt.Function("powers", R, RSeq)
    powers = kd.define(
        "powers",
        [x],
        smt.Lambda(
            [i],
            smt.If(
                i == 0,
                smt.RealVal(1),
                smt.If(i < 0, powers(x)[i + 1] / x, x * powers(x)[i - 1]),
            ),
        ),
    )
    # sin =


# %%

# deltaseq = kd.define("delta", [n, x], smt.Lambda([n], smt.If(n == 0, x, 0)))
# kd.prove(smt.ForAll([n], deltaseq(n, 0) == zero), by=[deltaseq.defn])
# kd.prove(
#    smt.ForAll([n, x, y], deltaseq(n, x) + deltaseq(n, y) == deltaseq(n, x + y)),
#    by=[deltaseq.defn, add.defn],
# )

# seqsum = smt.Function("seqsum", RSeq, R)
# seqsum_zero = kd.axiom(seqsum(zero) == 0)
# seqsum_delta = kd.axiom(smt.ForAll([n, x], seqsum(deltaseq(n, x)) == x))

# sum_converges = smt.Function("sum_converges", RSeq, smt.BoolSort())
# sum_converges_zero = kd.axiom(sum_converges(zero))
# sum_converges_delta = kd.axiom(smt.ForAll([n, x], sum_converges(deltaseq(n, x))))
# sum_converges_add = kd.axiom(
#    kd.QForAll([a, b], sum_converges(a), sum_converges(b), sum_converges(a + b))
# )

# seqsum_add = kd.axiom(
#    kd.QForAll(
#        [a, b],
#        sum_converges(a),
#        sum_converges(b),
#        seqsum(a + b) == seqsum(a) + seqsum(b),
#    )
# )

# psum = smt.Function("psum", RSeq, RSeq)  # partial sum


# has_seqlim = smt.Function("has_seqlim", RSeq, smt.BoolSort())

# %%
