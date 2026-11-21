"""Real sequences, convergence, limit algebra, and series."""
import kdrag as kd
from kdrag import FreshVars, QExists, QForAll, Theorem, define, define_const, prove
import kdrag.smt as smt
from kdrag.smt import (
    And,
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
    IntVal,
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
from kdrag.theories.real import rset


RSeq = real.RSeq
R = real.R

a, b, c = Consts("a b c", RSeq)
A, B, C = FreshVars("A B C", RSeq)
i, j, k, n, m, N = Ints("i j k n m N")
x, y, z, eps, delta, M = Reals("x y z eps delta M")

zero = define_const("RSeq.zero", K(IntSort(), RealVal(0)))
const = define("RSeq.const", [x], Lambda([i], x))
id_ = define_const("RSeq.id", Lambda([i], ToReal(i)))

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
sub_eq_add_neg = prove(A - B == A + -B, by=[sub.defn, add.defn, neg.defn]).forall(
    [A, B]
)

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


# Oriented partial sums: S[0] = 0 and S[n + 1] - S[n] = a[n].
cumsum = Function("cumsum", RSeq, RSeq)
cumsum = define(
    "cumsum",
    [a],
    Lambda(
        [i],
        If(
            i == 0,
            RealVal(0),
            If(i > 0, cumsum(a)[i - 1] + a[i - 1], cumsum(a)[i + 1] - a[i]),
        ),
    ),
)


@Theorem(ForAll([a, n], cumsum(a)[n + 1] == cumsum(a)[n] + a[n]))
def cumsum_succ(l):
    a, n = l.fixes()
    # Use the recurrence pointing toward zero on each side of the origin.
    l.cases(n >= 0, n < 0)
    _, step = kd.kernel.unfold(cumsum(a)[n + 1], [cumsum])
    l.auto(by=[step])
    _, step = kd.kernel.unfold(cumsum(a)[n], [cumsum])
    l.auto(by=[step])


@Theorem(ForAll(a, diff(cumsum(a)) == a))
def diff_cumsum(l):
    a = l.fix()
    l.ext()
    n = l.fix()
    l.auto(by=[diff.defn(cumsum(a)), cumsum_succ(a, n)])


@Theorem("forall (n : Int), cumsum zero n = 0")
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


@Theorem("forall (x : Real) (n : Int), cumsum (const x) n = n * x")
def cumsum_const(l):
    x, n = l.fixes()
    l.unfold(const)
    l.induct(n)
    # Step down from zero, base case, and step up from zero.
    l.fix()
    l.intros()
    l.unfold(cumsum)
    l.auto()
    l.unfold(cumsum)
    l.auto()
    l.fix()
    l.intros()
    l.unfold(cumsum)
    l.auto()


# TODO: cumsum id_ = n * (n - 1) / 2
# TODO: cumsum pownat = (1 - x^n) / (1 - x), when x != 1


@Theorem(ForAll([a, x], cumsum(smul(x, a)) == smul(x, cumsum(a))))
def cumsum_smul(l):
    a, x = l.fixes()
    l.ext()
    n = l.fix()
    l.induct(n)
    # Both directions use the same linearity argument for the recurrence.
    l.fix()
    l.intros()
    l.unfold(cumsum)
    l.auto(by=[smul.defn])
    l.unfold(cumsum)
    l.auto(by=[smul.defn])
    l.fix()
    l.intros()
    l.unfold(cumsum)
    l.auto(by=[smul.defn])


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
    l.intros()
    l.unfold(cumsum)
    l.auto(by=[add.defn(a, b)])

    # n == 0
    l.unfold(cumsum)
    l.auto(by=[add.defn(a, b)])

    # Positive step
    l.fix()
    l.intros()
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
    l.intros()
    i = l.fix()
    l.intros()
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


@Theorem(ForAll([a, n], finsum(a, n + 1) == finsum(a, n) + a[n]))
def finsum_succ(l):
    a, n = l.fixes()
    l.auto(by=[finsum.defn(a, n + 1), finsum.defn(a, n), cumsum_succ(a, n)])


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
    ForAll([a, n], ForAll(i, i >= 0, a[i] >= 0), n >= 0, finsum(a, n) >= 0)
)
def finsum_nonneg(l):
    a, n = l.fixes()
    l.intros()
    l.auto(by=[cumsum_mono(zero, a, n), cumsum_zero(n),
               finsum.defn(a, n), zero.defn])


@Theorem(
    QForAll([a, N], N >= 0,
            QForAll([n], n >= 0, n < N, abs(a)[n] <= finsum(abs(a), N)))
)
def abs_le_finsum_abs(l):
    a, N = l.fixes()
    l.intro()
    l.induct(N, using=int_.induct_nat)
    # No index lies in the empty prefix [0, 0).
    l.auto()
    N = l.fix()
    l.intros()
    n = l.fix()
    l.intros()
    l.have(finsum(abs(a), N + 1) == finsum(abs(a), N) + abs(a)[N],
           by=[finsum_succ(abs(a), N)])
    l.have(abs(a)[N] >= 0, by=[abs_ge_0(a, N)])
    l.cases(n < N, n == N)
    l.have(abs(a)[n] <= finsum(abs(a), N), by=[])
    l.auto()
    l.have(finsum(abs(a), N) >= 0, by=[finsum_nonneg(abs(a), N), abs_ge_0])
    l.auto()
    l.auto()


has_bound = define("has_bound", [a, M], QForAll([n], real.abs(a[n]) <= M))
is_bounded = define("is_bounded", [a], Exists([M], has_bound(a, M)))

is_monotone = define("is_monotone", [a], QForAll([n, m], n <= m, a[n] <= a[m]))
is_nonneg = define("is_nonneg", [a], QForAll([n], a[n] >= 0))

# The range relevant to convergence as n tends to positive infinity.
range_nonneg = define(
    "RSeq.range_nonneg", a, Lambda(x, Exists(n, n >= 0, a[n] == x))
)

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
        Exists([N], QForAll([n], n > N, real.abs(a[n] - y) < eps)),
    ),
)

# Eventually: a predicate on indices holds for every index past some cutoff.
P, Q = smt.Consts("P Q", smt.ArraySort(IntSort(), BoolSort()))
eventually = define("eventually", [P], Exists([N], ForAll([n], n > N, P[n])))


def near(a: smt.ArrayRef, y: smt.ExprRef, eps: smt.ExprRef) -> smt.QuantifierRef:
    """The index predicate `|a[n] - y| < eps`."""
    return Lambda([n], real.abs(a[n] - y) < eps)


@Theorem(
    ForAll(
        [a, y],
        smt.Eq(has_lim(a, y), ForAll([eps], eps > 0, eventually(near(a, y, eps)))),
    )
)
def has_lim_iff(l):
    l.fixes()
    l.unfold(has_lim)
    l.unfold(eventually)
    l.beta()
    l.auto()


@Theorem(ForAll([a, y, eps], has_lim(a, y), eps > 0, eventually(near(a, y, eps))))
def eventually_near(l):
    a, y, eps = l.fixes()
    l.rw(has_lim_iff(a, y))
    h = l.intro()
    l.specialize(h, eps)
    l.auto()


@Theorem(ForAll([P, Q], eventually(P), ForAll([n], P[n], Q[n]), eventually(Q)))
def eventually_mono(l):
    l.fixes()
    l.unfold(eventually)
    hp, _ = l.intros()
    N1 = l.obtain(hp)
    l.exists(N1)
    l.auto()


@Theorem(
    ForAll(
        [P, Q],
        eventually(P),
        eventually(Q),
        eventually(Lambda([n], And(P[n], Q[n]))),
    )
)
def eventually_and(l):
    l.fixes()
    l.unfold(eventually)
    hp, hq = l.intro(), l.intro()
    N1 = l.obtain(hp)
    N2 = l.obtain(hq)
    # Past both cutoffs.
    l.exists(If(N1 > N2, N1, N2))
    l.beta()
    l.auto()


@Theorem(ForAll([P], ForAll([n], n >= 0, P[n]), eventually(P)))
def eventually_of_forall_nonneg(l):
    l.fixes()
    l.unfold(eventually)
    l.intro()
    l.exists(IntVal(0))
    l.auto()


# convergent
is_conv = define("is_conv", [a], Exists([y], has_lim(a, y)))

# skolemize and define
(sk,), _pf = kd.kernel.obtain(Exists([y], has_lim(A, y)))
lim = define("lim", [A], sk)
lim_defn = prove(
    Implies(is_conv(A), has_lim(A, lim(A))), by=[lim.defn, _pf, is_conv.defn]
)


# kd.Lemma(has_lim(zero, 0)).unfold(has_lim).unfold(zero).unfold(real.abs)
lim_zero = prove(has_lim(zero, 0), by=[has_lim.defn, zero.defn, real.abs.defn])
lim_const = prove(has_lim(const(x), x), by=[has_lim.defn, const.defn, real.abs.defn])
has_lim_const = prove(
    ForAll([x], has_lim(const(x), x)), by=[has_lim.defn, const.defn, real.abs.defn]
)


@Theorem(has_lim(Lambda([n], RealVal(1) / n), RealVal(0)))
def has_lim_inv(l):
    l.unfold(has_lim)
    eps = l.fix()
    l.assumes(eps > 0)
    N = ToInt(1 / eps) + 1
    l.exists(N)
    l.fix()
    l.intro()
    l.unfold(real.abs)
    l.auto()


@Theorem("forall (a : RSeq) (x y : Real), has_lim a x -> has_lim a y -> x = y")
def lim_unique(l):
    a, x, y = l.fixes()
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


# Algebra of real sequence limits.
d = Const("d", RSeq)
r, u, v, w = Reals("r u v w")


@Theorem(ForAll([a, y], has_lim(a, y), ForAll(n, n >= 0, a[n] >= 0), y >= 0))
def lim_of_nonneg_seq(l):
    a, y = l.fixes()
    limit, nonneg = l.intro(), l.intro()
    l.unfold(has_lim, at=limit)
    l.contra()
    positive = l.have(-y > 0, by=[])
    cutoff = l.obtain(l.specialize(0, -y, positive))
    m = If(cutoff > 0, cutoff, 0) + 1
    l.specialize(nonneg, m)
    l.auto(by=[real.abs.defn(a[m] - y)])


@Theorem(
    ForAll(
        [a, x, r],
        has_lim(a, x),
        has_lim(smul(r, a), r * x),
    ),
)
def has_lim_smul(l):
    a, x, r = l.fixes()
    l.intro()
    l.rw(has_lim_iff)
    eps = l.fix()
    l.intro()
    # A positive denominator handles zero and nonzero scalars uniformly.
    eta = eps / (real.abs(r) + 1)
    l.have(eta > 0, by=[real.abs_pos(r)])
    l.have(eventually(near(a, x, eta)), by=[eventually_near(a, x, eta)])
    # Pointwise: |r a[m] - r x| = |r| |a[m] - x| < eps.
    l.have(ForAll([n], real.abs(a[n] - x) < eta, real.abs(smul(r, a)[n] - r * x) < eps))
    m = l.fix()
    l.intro()
    l.have(real.abs(r) * eta < eps, by=[real.abs_pos(r)])
    l.have(r * a[m] - r * x == r * (a[m] - x), by=[])
    l.auto(by=[smul.defn(r, a), real.abs_mul(r, a[m] - x), real.abs_pos(r)])
    l.auto(by=[eventually_mono(near(a, x, eta), near(smul(r, a), r * x, eps))])


@Theorem(
    ForAll(
        [a, b, x, y],
        has_lim(a, x),
        has_lim(b, y),
        has_lim(a + b, x + y),
    ),
)
def has_lim_add(l):
    a, b, x, y = l.fixes()
    l.intro(), l.intro()
    l.rw(has_lim_iff)
    eps = l.fix()
    l.intro()
    # Each sequence contributes half the error budget.
    e = eps / 2
    Pa, Pb = near(a, x, e), near(b, y, e)
    both = Lambda([n], And(Pa[n], Pb[n]))
    l.have(eventually(Pa), by=[eventually_near(a, x, e)])
    l.have(eventually(Pb), by=[eventually_near(b, y, e)])
    l.have(eventually(both), by=[eventually_and(Pa, Pb)])
    # Pointwise: the triangle inequality.
    l.have(
        ForAll(
            [n],
            And(real.abs(a[n] - x) < e, real.abs(b[n] - y) < e),
            real.abs((a + b)[n] - (x + y)) < eps,
        )
    )
    m = l.fix()
    l.intro()
    l.auto(by=[add.defn(a, b), real.abs_add(a[m] - x, b[m] - y)])
    l.auto(by=[eventually_mono(both, near(a + b, x + y, eps))])


@Theorem(ForAll([a, x], has_lim(a, x), has_lim(-a, -x)))
def has_lim_neg(l):
    a, x = l.fixes()
    l.intro()
    l.rw(has_lim_iff)
    eps = l.fix()
    l.intro()
    l.have(eventually(near(a, x, eps)), by=[eventually_near(a, x, eps)])
    # Pointwise: |-a[m] - -x| = |a[m] - x|.
    l.have(ForAll([n], real.abs(a[n] - x) < eps, real.abs((-a)[n] - -x) < eps))
    l.unfold(neg)
    l.beta()
    m = l.fix()
    l.intro()
    l.auto(by=[real.abs_neg(a[m] - x)])
    l.auto(by=[eventually_mono(near(a, x, eps), near(-a, -x, eps))])


@Theorem(
    ForAll(
        [a, b, x, y],
        has_lim(a, x),
        has_lim(b, y),
        has_lim(a - b, x - y),
    ),
)
def has_lim_sub(l):
    a, b, x, y = l.fixes()
    l.rw(sub_eq_add_neg)
    l.auto(by=[has_lim_add(a, -b, x, -y), has_lim_neg(b, y)])


@Theorem(
    ForAll(
        [a, b, x, y],
        has_lim(a, x),
        has_lim(b, y),
        ForAll(n, n >= 0, a[n] <= b[n]),
        x <= y,
    ),
)
def le_of_has_lim_of_has_lim(l):
    """Limits preserve non-strict inequalities between sequences."""
    a, b, x, y = l.fixes()
    l.auto(
        by=[
            sub.defn(b, a),
            has_lim_sub(b, a, y, x),
            lim_of_nonneg_seq(b - a, y - x),
        ]
    )


@Theorem(ForAll([a, x, r], has_lim(a, x), ForAll(n, n >= 0, a[n] <= r), x <= r))
def le_of_has_lim(l):
    a, x, r = l.fixes()
    l.auto(
        by=[
            le_of_has_lim_of_has_lim(a, const(r), x, r),
            has_lim_const(r),
            const.defn(r),
        ]
    )


@Theorem(ForAll([a, x, r], has_lim(a, x), ForAll(n, n >= 0, r <= a[n]), r <= x))
def ge_of_has_lim(l):
    a, x, r = l.fixes()
    l.auto(
        by=[
            le_of_has_lim_of_has_lim(const(r), a, r, x),
            has_lim_const(r),
            const.defn(r),
        ]
    )


@Theorem(
    ForAll(
        [a, b, d, x],
        has_lim(a, x),
        has_lim(d, x),
        ForAll(n, n >= 0, And(a[n] <= b[n], b[n] <= d[n])),
        has_lim(b, x),
    ),
)
def has_lim_squeeze(l):
    """Squeeze theorem: a sequence trapped between two with limit x has limit x."""
    a, b, d, x = l.fixes()
    l.intro(), l.intro(), l.intro()
    l.rw(has_lim_iff)
    eps = l.fix()
    l.intro()
    Pa, Pd = near(a, x, eps), near(d, x, eps)
    between = Lambda([n], And(a[n] <= b[n], b[n] <= d[n]))
    both = Lambda([n], And(Pa[n], Pd[n]))
    trapped = Lambda([n], And(both[n], between[n]))
    l.have(eventually(Pa), by=[eventually_near(a, x, eps)])
    l.have(eventually(Pd), by=[eventually_near(d, x, eps)])
    l.have(eventually(between), by=[eventually_of_forall_nonneg(between)])
    l.have(eventually(both), by=[eventually_and(Pa, Pd)])
    l.have(eventually(trapped), by=[eventually_and(both, between)])
    # Pointwise: b[m] lies between a[m] and d[m], both within eps of x.
    l.have(
        ForAll(
            [n],
            And(real.abs(a[n] - x) < eps, real.abs(d[n] - x) < eps),
            And(a[n] <= b[n], b[n] <= d[n]),
            real.abs(b[n] - x) < eps,
        )
    )
    m = l.fix()
    l.intro(), l.intro()
    l.auto(by=[real.abs.defn(a[m] - x), real.abs.defn(d[m] - x), real.abs.defn(b[m] - x)])
    l.auto(by=[eventually_mono(trapped, near(b, x, eps))])


@Theorem(
    ForAll(
        [a, b, x, y],
        has_lim(a, x),
        has_lim(b, y),
        has_lim(a * b, x * y),
    ),
)
def has_lim_mul(l):
    a, b, x, y = l.fixes()
    l.intro(), l.intro()
    l.rw(has_lim_iff)
    eps = l.fix()
    l.intro()
    # Keep both errors below one and small enough for the product estimate.
    eta = real.min(1, eps / (2 * (real.abs(x) + real.abs(y) + 1)))
    l.have(eta > 0, by=[real.abs_pos(x), real.abs_pos(y), real.min.defn])
    Pa, Pb = near(a, x, eta), near(b, y, eta)
    both = Lambda([n], And(Pa[n], Pb[n]))
    l.have(eventually(Pa), by=[eventually_near(a, x, eta)])
    l.have(eventually(Pb), by=[eventually_near(b, y, eta)])
    l.have(eventually(both), by=[eventually_and(Pa, Pb)])
    # Pointwise: expand a[m] b[m] - x y and bound each term.
    l.have(
        ForAll(
            [n],
            And(real.abs(a[n] - x) < eta, real.abs(b[n] - y) < eta),
            real.abs((a * b)[n] - x * y) < eps,
        )
    )
    m = l.fix()
    l.intro()
    l.have(
        And(eta <= 1, 2 * eta * (real.abs(x) + real.abs(y) + 1) <= eps),
        by=[real.abs_pos(x), real.abs_pos(y), real.min.defn],
    )
    u, v = a[m] - x, b[m] - y
    da, db = real.abs(u), real.abs(v)
    error_bound = da * db + real.abs(y) * da + real.abs(x) * db
    l.have(a[m] * b[m] - x * y == u * v + y * u + x * v, by=[])
    l.have(
        real.abs(a[m] * b[m] - x * y) <= error_bound,
        by=[
            real.abs_add(u * v + y * u, x * v),
            real.abs_add(u * v, y * u),
            real.abs_mul(u, v),
            real.abs_mul(y, u),
            real.abs_mul(x, v),
        ],
    )
    l.have(error_bound < eps, by=[real.abs_pos(u), real.abs_pos(v), real.abs_pos(x), real.abs_pos(y)])
    l.auto(by=[mul.defn(a, b)])
    l.auto(by=[eventually_mono(both, near(a * b, x * y, eps))])


@Theorem(
    ForAll(
        [u, v, w, z],
        And(v != 0, z != 0),
        (u / v) + -1 * (w / z) == (u - w) / v + w * ((z - v) / (v * z)),
    )
)
def div_decomp(l):
    u, v, w, z = l.fixes()
    l.intro()
    l.auto()


@Theorem(
    ForAll([a, b, x, y], has_lim(a, x), has_lim(b, y), y != 0, has_lim(a / b, x / y))
)
def has_lim_div(l):
    a, b, x, y = l.fixes()
    l.intro(), l.intro(), l.intro()
    l.rw(has_lim_iff)
    eps = l.fix()
    l.intro()
    # Keep the denominator away from zero and split the quotient error.
    Y, X = real.abs(y), real.abs(x)
    ea = eps * Y / 4
    eb = real.min(Y / 2, eps * Y * Y / (4 * (X + 1)))
    l.have(Y > 0, by=[real.abs_pos_iff(y)])
    l.have(ea > 0, by=[])
    l.have(eb > 0, by=[real.abs_pos(x), real.min.defn])
    Pa, Pb = near(a, x, ea), near(b, y, eb)
    both = Lambda([n], And(Pa[n], Pb[n]))
    l.have(eventually(Pa), by=[eventually_near(a, x, ea)])
    l.have(eventually(Pb), by=[eventually_near(b, y, eb)])
    l.have(eventually(both), by=[eventually_and(Pa, Pb)])
    # Pointwise: split a[m]/b[m] - x/y into a numerator and a denominator error.
    l.have(
        ForAll(
            [n],
            And(real.abs(a[n] - x) < ea, real.abs(b[n] - y) < eb),
            real.abs((a / b)[n] - x / y) < eps,
        )
    )
    l.unfold(div)
    l.beta()
    m = l.fix()
    l.intro()

    am, bm = a[m], b[m]
    da, db, B = real.abs(am - x), real.abs(bm - y), real.abs(bm)
    l.have(And(db < Y / 2, db * (4 * (X + 1)) < eps * Y * Y), by=[real.min.defn, real.abs_pos(x)])
    l.have(real.abs(y - bm) == db, by=[real.abs_neg(bm - y)])
    l.have(Y <= db + B, by=[real.abs_triangle(y, RealVal(0), bm)])
    l.have(B > Y / 2, by=[])
    l.have(bm != 0, by=[real.abs_pos_iff(bm)])
    t1 = (am - x) / bm
    t2 = x * ((y - bm) / (bm * y))
    decomp = l.have(am / bm - x / y == t1 + t2, by=[div_decomp(am, bm, x, y)])
    l.have(real.abs(t1) == da / B, by=[real.abs_div(am - x, bm)])
    l.have(
        real.abs(t2) == X * (db / (B * Y)),
        by=[real.abs_mul(x, (y - bm) / (bm * y)), real.abs_div(y - bm, bm * y), real.abs_mul(bm, y)],
    )
    l.have(da / B < eps / 2, by=[])
    l.have(X * (db / (B * Y)) < eps / 2, by=[real.abs_pos(x), real.abs_pos(bm - y)])
    bound = l.have(real.abs(t1 + t2) < eps, by=[real.abs_add(t1, t2)])
    # Discharge congruence with just the equality and the scalar bound.
    result = real.abs(am / bm - x / y) < eps
    l.auto(by=[prove(Implies(And(decomp, bound), result))])
    l.auto(by=[eventually_mono(both, near(a / b, x / y, eps))])


@Theorem(
    ForAll([a, x], is_monotone(a), rset.is_lub(range_nonneg(a), x), has_lim(a, x))
)
def has_lim_of_monotone_of_is_lub(l):
    a, s = l.fixes()
    l.unfold(is_monotone)
    monotone, _ = l.intros()
    values = range_nonneg(a)
    l.have(rset.is_ub(values, s), by=[rset.is_ub_of_is_lub(values, s)])
    l.unfold(has_lim)
    eps = l.fix()
    l.intro()
    # Anything strictly below the supremum fails to bound the range.
    l.have(smt.Not(rset.is_ub(values, s - eps)),
           by=[rset.le_of_is_lub_of_is_ub(values, s, s - eps)])
    witness = l.have(Exists(n, n >= 0, s - eps < a[n]),
                     by=[rset.is_ub.defn(values, s - eps), range_nonneg.defn(a)])
    N = l.obtain(witness)
    l.exists(N)
    k = l.fix()
    l.intro()
    # The entire tail is trapped between a[N] > s-eps and the supremum s.
    l.specialize(monotone, N, k)
    l.have(values[a[k]], by=[range_nonneg.defn(a)])
    l.have(a[k] <= s, by=[rset.le_of_mem_of_is_ub(values, a[k], s)])
    l.auto(by=[real.abs.defn(a[k] - s)])


@Theorem(
    ForAll(a, is_monotone(a), rset.bdd_above(range_nonneg(a)),
           Exists(x, has_lim(a, x)))
)
def exists_has_lim_of_monotone_of_bdd_above(l):
    a = l.fix()
    l.intros()
    values = range_nonneg(a)
    l.have(values[a[0]], by=[range_nonneg.defn(a)])
    l.have(Exists(x, values[x]), by=[])
    supremum = l.have(Exists(x, rset.is_lub(values, x)),
                      by=[rset.exists_is_lub_of_bdd_above(values)])
    s = l.obtain(supremum)
    l.exists(s)
    l.auto(by=[has_lim_of_monotone_of_is_lub(a, s)])


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
