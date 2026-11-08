"""Algebra of real sequence limits."""

from kdrag import Theorem
from kdrag.smt import And, Consts, ForAll, If, Implies, Reals
from kdrag.theories.real import RSeq, abs, min
from kdrag.theories.real.seq import add, has_lim, mul, smul


a, b = Consts("a b", RSeq)
x, y, c = Reals("x y c")
u, v, w, z = Reals("u v w z")


@Theorem(
    ForAll(
        [a, x, c],
        has_lim(a, x),
        has_lim(smul(c, a), c * x),
    ),
)
def has_lim_smul(l):
    a, x, c = l.fixes()
    l.unfold(has_lim)
    ha = l.intros()
    eps = l.fix()
    l.intros()
    # A positive denominator handles zero and nonzero scalars uniformly.
    eta = eps / (abs(c) + 1)
    l.have(eta > 0, by=[abs.defn])
    N = l.obtain(l.forward(l.specialize(ha, eta)))
    l.exists(N)
    m = l.fix()
    l.intros()
    l.have(abs(a[m] - x) < eta, by=[])
    l.have(abs(c) * eta < eps, by=[abs.defn])
    l.auto(by=[smul.defn(c, a), abs.defn])


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
    l.unfold(has_lim)
    ha, hb = l.andE(l.intros())
    eps = l.fix()
    l.intros()
    # Each sequence contributes half the error budget.
    N1 = l.obtain(l.forward(l.specialize(ha, eps / 2)))
    N2 = l.obtain(l.forward(l.specialize(hb, eps / 2)))
    l.exists(If(N1 > N2, N1, N2))
    m = l.fix()
    l.intros()
    l.have(abs(a[m] - x) < eps / 2, by=[])
    l.have(abs(b[m] - y) < eps / 2, by=[])
    l.have(
        abs((a[m] + b[m]) - (x + y)) <= abs(a[m] - x) + abs(b[m] - y),
        by=[abs.defn],
    )
    l.auto(by=[add.defn(a, b)])


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
    l.unfold(has_lim)
    ha, hb = l.andE(l.intros())
    eps = l.fix()
    l.intros()
    # Keep both errors below one and small enough for the product estimate.
    eta = min(1, eps / (2 * (abs(x) + abs(y) + 1)))
    l.have(eta > 0, by=[abs.defn, min.defn])
    N1 = l.obtain(l.forward(l.specialize(ha, eta)))
    N2 = l.obtain(l.forward(l.specialize(hb, eta)))
    l.exists(If(N1 > N2, N1, N2))
    m = l.fix()
    l.intros()
    l.have(abs(a[m] - x) < eta, by=[])
    l.have(abs(b[m] - y) < eta, by=[])
    l.have(
        And(eta <= 1, 2 * eta * (abs(x) + abs(y) + 1) <= eps),
        by=[abs.defn, min.defn],
    )
    da, db = abs(a[m] - x), abs(b[m] - y)
    error_bound = da * db + abs(y) * da + abs(x) * db
    l.have(abs(a[m] * b[m] - x * y) <= error_bound, by=[abs.defn])
    l.have(error_bound < eps, by=[abs.defn])
    l.auto(by=[mul.defn(a, b)])


@Theorem(
    ForAll(
        [u, v, w, z],
        Implies(
            And(v != 0, z != 0),
            (u / v) + -1 * (w / z) == (u - w) / v + w * ((z - v) / (v * z)),
        ),
    )
)
def div_decomp(l):
    u, v, w, z = l.fixes()
    l.intros()
    l.auto()
