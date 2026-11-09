# %%
import kdrag as kd
from kdrag import FreshVars, QExists, QForAll, Theorem, define, prove
import kdrag.smt as smt
from kdrag.smt import (
    Array,
    ArraySort,
    BoolSort,
    Const,
    Consts,
    Exists,
    ForAll,
    Function,
    If,
    Implies,
    Int,
    IntSort,
    Ints,
    K,
    Lambda,
    Map,
    RealSort,
    RealVal,
    Reals,
    ToInt,
    ToReal,
)

import kdrag.theories.int as int_
import kdrag.theories.real as real


RSeq = real.RSeq
R = real.R

a, b, c = Consts("a b c", RSeq)
A, B, C = FreshVars("A B C", RSeq)
i, j, k, n, m, N = Ints("i j k n m N")
x, y, z, eps, delta, M = Reals("x y z eps delta M")

zero = define("RSeq.zero", [], K(IntSort(), RealVal(0)))
const = define("RSeq.const", [x], Lambda([i], x))
id_ = define("RSeq.id", [], Lambda([i], ToReal(i)))
assert isinstance(id_, smt.ExprRef)  # for typechecker

geom = define("geom", [x], Lambda([i], real.pownat(x, i)))

S = Array("S", IntSort(), BoolSort())
ind = define(
    "ind", [S], Lambda([i], If(S[i], RealVal(1), RealVal(0)))
)  # indicator sequence / iverson bracket

F = Array("F", IntSort(), IntSort())
dommap = define("dommap", [F, a], Lambda([i], a[F[i]]))

# Domain operations
shift = define("RSeq.shift", [a, n], Lambda([i], a[i - n]))
delay = define("delay", [a], shift(a, 1))
rev = define("RSeq.rev", [a], Lambda([i], a[-i]))
dilate = define("dilate", [a, n], Lambda([i], a[i / n]))
decimate = define("decimate", [a, n], Lambda([i], a[i * n]))

f = Array("f", kd.R, kd.R)
iterate = Function("iterate", ArraySort(kd.R, kd.R), kd.R, ArraySort(kd.R, kd.R))
iterate = define("iterate", [f, x], Lambda([i], If(i <= 0, x, f[iterate(f, x)[i - 1]])))

mask = Array("mask", IntSort(), BoolSort())
where = define("where", [mask, a, b], Lambda([i], If(mask[i], a[i], b[i])))
krondelta = define("krondelta", [n], Lambda([i], If(i == n, RealVal(1), RealVal(0))))
kron_same = prove(ForAll([n], krondelta(n)(n) == 1), by=[krondelta.defn])
kron_diff = prove(ForAll([n, m], n != m, krondelta(n)(m) == 0), by=[krondelta.defn])

pos = define("pos", [a], Lambda([i], If(i >= 0, a[i], RealVal(0))))
# arange = kd.define("arange", [n], smt.Lambda([i], smt.ToReal(i) * smt.ToReal(n >= i)))

# numpy names
zeros = zero
full = const
roll = shift

diff = define("diff", [a], Lambda([i], a[i + 1] - a[i]))


add = kd.notation.add.define([a, b], Lambda([i], a[i] + b[i]))
# add = kd.define("add", [a, b], smt.Map(real.add, a, b))
kd.notation.add.register(RSeq, add)
add_comm = prove(
    A + B == B + A, by=[add.defn(B, A), add.defn(A, B), real.add_comm]
).forall([A, B])
add_assoc = prove(
    (A + B) + C == A + (B + C),
    unfold=1,
    by=[real.add_assoc],
).forall([A, B, C])
# kd.Lemma(diff(cumsum(A)) == A)
add_zero = prove(A + zero == A, by=[add.defn, zero.defn]).forall([A])


sub = kd.notation.sub.define([a, b], Lambda([i], a[i] - b[i]))
mul = kd.notation.mul.define([a, b], Lambda([i], a[i] * b[i]))

mul_comm = prove(
    A * B == B * A, by=[mul.defn(B, A), mul.defn(A, B), real.mul_comm]
).forall([A, B])
mul_assoc = prove(
    (A * B) * C == A * (B * C),
    unfold=1,
    by=[real.mul_assoc],
).forall([A, B, C])

mul_zero = prove(A * zero == zero, by=[mul.defn, zero.defn]).forall([A])
mul_one = prove(A * const(1) == A, by=[mul.defn, const.defn, real.mul_one]).forall([A])

add_mul = prove((A + B) * C == A * C + B * C, by=[add.defn, mul.defn]).forall([A, B, C])
mul_add = prove(A * (B + C) == A * B + A * C, by=[add.defn, mul.defn]).forall([A, B, C])

div = kd.notation.div.define([a, b], Lambda([i], a[i] / b[i]))
neg = kd.notation.neg.define([a], Lambda([i], -a[i]))

smul = define("RSeq.smul", [x, a], Lambda([n], x * a[n]))


@Theorem(ForAll([x, a, b], smul(x, a) * b == smul(x, a * b)))
def smul_mul(l):
    x, a, b = l.fixes()
    l.unfold(smul)
    l.unfold(mul)
    l.ext()
    l.auto()


rev_rev = prove(rev(rev(A)) == A, by=[rev.defn]).forall([A])
shift_shit = prove(
    ForAll([n, m, a], shift(shift(a, n), m) == shift(a, n + m)), by=[shift.defn]
)
rev_shift = prove(
    ForAll([n, a], rev(shift(a, n)) == shift(rev(a), -n)), by=[shift.defn, rev.defn]
)
rev_zero = prove(rev(zero) == zero, by=[rev.defn, zero.defn])
rev_const = prove(ForAll([x], rev(const(x)) == const(x)), by=[rev.defn, const.defn])
rev_id = prove(rev(id_) == -id_, by=[rev.defn, id_.defn, neg.defn])


def test():
    """
    >>> True
    True
    """


cumsum = Function("cumsum", RSeq, RSeq)
cumsum = define(
    "cumsum",
    [a],
    Lambda(
        [i],
        If(  # Maybe this is a badly shifted definition
            i == 0,
            a[0],
            If(i > 0, cumsum(a)[i - 1] + a[i], -cumsum(a)[i + 1] - a[i + 1]),
        ),
    ),
)


@Theorem("forall (n : Int), cumsum zero n = 0")
def cumsum_zero(l):
    n = l.fix()
    l.unfold(zero)
    l.induct(n)

    # n < 0
    l.fix()
    l.intro()
    l.intro()
    l.unfold(cumsum)
    l.auto()

    # n == 0
    l.unfold(cumsum)
    l.auto()

    # n > 0
    l.fix()
    l.intro()
    l.intro()
    l.unfold(cumsum)
    l.auto()


@Theorem(
    "forall (x : Real) (n : Int), n >= 0 -> cumsum (const x) n = (n + 1) * x"
)  # TODO: fix for n < 0. Wrong definition?
def cumsum_const(l):
    x, n = l.fixes()
    l.unfold(const)
    l.induct(n)

    # n < 0
    # l.fix()
    # l.intro()
    # l.unfold(cumsum)
    # l.simp()
    l.auto()

    # n == 0
    l.unfold(cumsum)
    l.auto()

    # n > 0
    n = l.fix()
    l.intro()
    l.intro()
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


cumsum_smul = prove(
    ForAll([a, x], cumsum(smul(x, a)) == smul(x, cumsum(a))), admit=True
)
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
    l.intro()
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


@Theorem(
    "forall (a b : RSeq) (m : Int), (forall (n : Int), n >= 0 -> a n <= b n) -> m >= 0 -> cumsum a m <= cumsum b m"
)
def cumsum_mono(l):
    a, b, m = l.fixes()
    l.intro()
    l.induct(m)
    _n = l.fix()
    l.auto()

    # n == 0
    l.auto(by=[cumsum.defn])

    # n > 0
    _n = l.fix()
    l.intro()
    l.intro()
    l.simp()
    l.intro()
    l.unfold(cumsum)
    l.auto(by=[cumsum.defn])


@Theorem("forall (a b : RSeq) (n : Int), cumsum (a + b) n = cumsum a n + cumsum b n")
def cumsum_add(l):
    a, b, n = l.fixes()
    l.induct(n)

    # Unfold only the outer recurrence, preserving the induction hypothesis.
    # The negative and positive steps both reduce to linear arithmetic.
    l.fix()
    l.intro()
    l.intro()
    l.unfold(cumsum)
    l.auto(by=[add.defn(a, b)])

    # n == 0
    l.unfold(cumsum)
    l.auto(by=[add.defn(a, b)])

    # Positive step
    l.fix()
    l.intro()
    l.intro()
    l.unfold(cumsum)
    l.auto(by=[add.defn(a, b)])


max = Function("max", RSeq, RSeq)
max = define(
    "max",
    [a],
    Lambda(
        [i],
        If(
            i == 0,
            a[0],
            If(
                i > 0,
                real.max(max(a)[i - 1], a[i]),
                real.max(max(a)[i + 1], a[i]),
            ),
        ),
    ),
)


@Theorem(ForAll([a, i], max(a)[i] >= a[i]))
def max_ge_self(l):
    a, i = l.fixes()
    l.unfold(max)
    l.auto(by=[real.max_ge_2])


@Theorem(
    QForAll(
        [a, n],
        n >= 0,
        QForAll([i], i >= 0, i <= n, a[i] <= max(a)[n]),
    )
)
def max_prefix_bound(l):
    a, n = l.fixes()
    # l.intro()
    l.induct(n)  # Some weird stuff happened here
    l.auto()  # n < 0
    l.auto(by=[max.defn])  # n == 0. Kind of weird that we lose the equality...
    n = l.fix()
    l.intro()
    l.intro()
    l.simp(at=-1)
    i = Int("i")
    l.have(ForAll([i], i >= 0, i <= n, a[i] <= max(a)[n]), by=[])
    l.intro()
    i = l.fix()
    l.intro()
    l.specialize(2, i)
    l.unfold(max)
    l.simp()
    l.unfold(real.max)
    l.auto()


max_bound = prove(
    QForAll([a, n, i], n >= 0, i >= 0, i <= n, a[i] <= max(a)[n]),
    by=[max_prefix_bound],
)


@Theorem(
    QForAll(
        [a, n],
        n <= 0,
        QForAll([i], n <= i, i <= 0, a[i] <= max(a)[n]),
    )
)
def max_suffix_bound(l):
    a, n = l.fixes()
    l.induct(n)
    # step: n <= 0 -> n - 1
    n = l.fix()
    l.intro()
    l.intro()
    l.intro()
    i = l.fix()
    l.intro()
    l.intro()
    l.cases(i == n - 1)
    l.have(i == n - 1, by=[])
    l.unfold(max)
    l.simp()
    l.unfold(real.max)
    l.auto(by=[real.max_ge_2])
    l.have(i != n - 1, by=[])
    l.have(n <= i, by=[])
    j = Int("j")
    l.have(QForAll([j], n <= j, j <= 0, a[j] <= max(a)[n]), by=[])
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


Sum = Function("Sum", RSeq, IntSort(), IntSort(), R)
finsum = define("finsum", [a, n], cumsum(a)[n])


@Theorem(QForAll([a, n], n >= 0, finsum(a, n + 1) == finsum(a, n) + a[n + 1]))
def finsum_succ(l):
    a, n = l.fixes()
    # Use the recurrence at this index, rather than an equality of whole arrays.
    _, step = kd.kernel.unfold(cumsum(a)[n + 1], [cumsum])
    l.auto(by=[finsum.defn(a, n + 1), finsum.defn(a, n), step])


@Theorem(ForAll([a, x, n], finsum(smul(x, a), n) == x * finsum(a, n)))
def finsum_smul(l):
    a, x, n = l.fixes()
    l.unfold(finsum)
    l.rw(cumsum_smul)
    l.unfold(smul)
    l.auto()


finsum_add = prove(
    QForAll([a, b, n], finsum(a + b, n) == finsum(a, n) + finsum(b, n)),
    by=[finsum.defn, cumsum_add],
)

finsum_zero = prove(
    QForAll([n], finsum(zero, n) == 0),
    by=[finsum.defn, cumsum_zero],
)

dot = define("rseq.dot", [n, a, b], finsum(a * b, n))

dot_comm = prove(
    QForAll([a, b, n], dot(n, a, b) == dot(n, b, a)),
    by=[dot.defn, mul_comm],
)

dot_smul = prove(
    QForAll([x, a, b, n], dot(n, smul(x, a), b) == x * dot(n, a, b)),
    by=[dot.defn, finsum_smul, smul_mul],
)


@Theorem(QForAll([a, b, c, n], dot(n, a + b, c) == dot(n, a, c) + dot(n, b, c)))
def dot_add(l):
    a, b, c, n = l.fixes()
    l.unfold(dot)
    l.rw(add_mul)
    l.rw(finsum_add)
    l.auto()


@Theorem(
    QForAll([a, n], dot(n, zero, a) == 0),
)
def dot_zero(l):
    a, n = l.fixes()
    l.unfold(dot)
    l.rw(mul_comm)
    l.rw(mul_zero)
    l.rw(finsum_zero)
    l.auto()


# dot(v,v) >= 0
# dot(v,v) == 0 iff v == 0
# dot(zero, x) = 0

# norm
# cauchy schwarz
# triangle inequality


outer = define("rseq.outer", [a, b], Lambda([i, j], a[i] * b[j]))
eye = define("eye", [n], Lambda([i, j], If(i == j, RealVal(1), RealVal(0))))
ehat = krondelta


# dot(m, ehat(n), a) == If(m >= n, a[n], 0)
# matrixsum ehat = id


sin = define("rseq.sin", [a], Map(real.sin, a))
cos = define("rseq.cos", [a], Map(real.cos, a))

abs = define("rseq.abs", [a], Map(real.abs, a))
abs_ext = prove(ForAll([a, n], abs(a)[n] == real.abs(a[n])), by=[abs.defn])
abs_ge_0 = prove(
    QForAll([a, n], abs(a)[n] >= 0),
    by=[abs_ext, real.abs_pos],
)


@Theorem(
    QForAll(
        [a, N],
        N >= 0,
        QForAll([n], n >= 0, n <= N, abs(a)[n] <= finsum(abs(a), N)),
    )
)
def abs_le_finsum_abs(l):
    a, N = l.fixes()

    l.induct(N, using=int_.induct_nat)
    # base case: N = 0
    l.intro()
    n = l.fix()
    l.intro()
    l.intro()
    l.have(n == 0, by=[])
    l.rw(-1)
    l.unfold(finsum)
    l.unfold(cumsum)
    l.simp()
    l.auto()

    # step: N >= 0, IH -> N + 1
    N = l.fix()
    l.intro()
    l.intro()
    l.intro()

    n = l.fix()
    l.intro()
    l.intro()

    # Establish the shared recurrence before splitting the two cases.
    l.have(
        finsum(abs(a), N + 1) == finsum(abs(a), N) + abs(a)[N + 1],
        by=[finsum_succ(abs(a), N)],
    )
    l.have(abs(a)[N + 1] >= 0, by=[abs_ge_0(a, N + 1)])

    # Case split: n <= N or n = N + 1
    l.cases(n <= N)

    # n <= N: use IH and monotonicity of finsum
    l.have(abs(a)[n] <= finsum(abs(a), N), by=[])
    l.have(finsum(abs(a), N) <= finsum(abs(a), N + 1), by=[])
    l.auto()

    # n > N: then n = N + 1
    l.have(n == N + 1, by=[])
    l.rw(-1)
    l.have(abs(a)[0] <= finsum(abs(a), N), by=[])
    l.have(abs(a)[0] >= 0, by=[abs_ge_0])
    l.have(finsum(abs(a), N + 1) >= abs(a)[N + 1], by=[])
    l.auto()


has_bound = define("has_bound", [a, M], QForAll([n], real.abs(a[n]) <= M))
is_bounded = define("is_bounded", [a], Exists([M], has_bound(a, M)))

is_monotone = define("is_monotone", [a], QForAll([n, m], n <= m, a[n] <= a[m]))
is_nonneg = define("is_nonneg", [a], QForAll([n], a[n] >= 0))

# https://en.wikipedia.org/wiki/Cauchy_sequence

mod = Const("mod", ArraySort(RealSort(), IntSort()))

is_cauchy = define(
    "is_cauchy",
    [a],
    QForAll(
        [eps],
        eps > 0,
        Exists([N], QForAll([m, k], m > N, k > N, real.abs(a[m] - a[k]) < eps)),
    ),
)
cauchy_mod = define(
    "cauchy_mod",
    [a, mod],
    QForAll(
        [eps],
        eps > 0,
        QForAll([m, k], m > mod[eps], k > mod[eps], real.abs(a[m] - a[k]) < eps),
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
has_lim = define(
    "has_lim",
    [a, y],
    QForAll(
        [eps],
        eps > 0,
        QExists([N], QForAll([n], n > N, real.abs(a[n] - y) < eps)),
    ),
)

# convergent
is_conv = define("is_conv", [a], Exists([y], has_lim(a, y)))

# skolemize and define
(sk,), pf = kd.kernel.obtain(Exists([y], has_lim(A, y)))
lim = define("lim", [A], sk)
lim_defn = prove(
    Implies(is_conv(A), has_lim(A, lim(A))), by=[lim.defn, pf, is_conv.defn]
)


# kd.Lemma(has_lim(zero, 0)).unfold(has_lim).unfold(zero).unfold(real.abs)
lim_zero = prove(has_lim(zero, 0), by=[has_lim.defn, zero.defn, real.abs.defn])
lim_const = prove(has_lim(const(x), x), by=[has_lim.defn, const.defn, real.abs.defn])


@Theorem(has_lim(Lambda([n], RealVal(1) / n), RealVal(0)))
def has_lim_inv(l):
    l.unfold(has_lim)
    eps = l.fix()
    l.assumes(eps > 0)
    l.exists(ToInt(1 / eps) + 1)
    n = l.fix()
    l.assumes(n > ToInt(1 / eps) + 1)
    l.unfold(real.abs)
    l.auto()


@Theorem("forall (a : RSeq) (x y : Real), has_lim a x -> has_lim a y -> x = y")
def lim_unique(l):
    a, x, y = l.fixes()
    l.intro()
    l.intro()
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
    n1 = Int("N")  # "N1" is problem for alpha rename
    n2 = Int("N")  # "N2" is problem for alpha rename
    n = Int("n")
    exists_x = QExists(
        [n1],
        QForAll([n], n > n1, real.abs(a[n] - x) < eps),
    )
    exists_y = QExists(
        [n2],
        QForAll([n], n > n2, real.abs(a[n] - y) < eps),
    )
    l.have(exists_x, by=[])  # unstable due to alpha rename?
    N1 = l.obtain(exists_x)
    l.have(exists_y, by=[])
    N2 = l.obtain(exists_y)
    N = If(N1 > N2, N1, N2) + 1
    forall_x = QForAll([n], n > N1, real.abs(a[n] - x) < eps)
    forall_y = QForAll([n], n > N2, real.abs(a[n] - y) < eps)
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


has_sum = define("has_sum", [a, y], has_lim(cumsum(a), y))
is_summable = define("is_summable", [a], Exists([y], has_sum(a, y)))


class Series:
    # https://www.cs.dartmouth.edu/~doug/powser.html
    powers = Function("powers", R, RSeq)
    powers = define(
        "powers",
        [x],
        Lambda(
            [i],
            If(
                i == 0,
                RealVal(1),
                If(i < 0, powers(x)[i + 1] / x, x * powers(x)[i - 1]),
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
