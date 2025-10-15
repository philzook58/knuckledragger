# %%
import kdrag as kd
import kdrag.smt as smt

import kdrag.theories.real as real


RSeq = real.RSeq
R = real.R

a, b, c = smt.Consts("a b c", RSeq)
A, B, C = kd.FreshVars("A B C", RSeq)
i, j, k, n, m, N = smt.Ints("i j k n m N")
x, y, z, eps, delta = smt.Reals("x y z eps delta")

zero = kd.define("zero", [], smt.K(smt.IntSort(), smt.RealVal(0)))
const = kd.define("const", [x], smt.Lambda([i], x))
id_ = kd.define("id", [], smt.Lambda([i], smt.ToReal(i)))
assert isinstance(id_, smt.ExprRef)

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
        smt.If(
            i == 0,
            a[0],
            smt.If(i > 0, cumsum(a)[i - 1] + a[i], -cumsum(a)[i + 1] - a[i]),
        ),
    ),
)


Sum = smt.Function("Sum", RSeq, smt.IntSort(), smt.IntSort(), R)
finsum = kd.define("finsum", [a, n], cumsum(a)[n])


sin = kd.define("sin", [a], smt.Map(real.sin, a))
cos = kd.define("cos", [a], smt.Map(real.cos, a))


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
kd.prove(has_lim(zero, 0), by=[has_lim.defn, zero.defn, real.abs.defn])
kd.prove(has_lim(const(x), x), by=[has_lim.defn, const.defn, real.abs.defn])


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
