"""Algebra of real sequence limits."""

from kdrag import Theorem, prove
from kdrag.smt import And, Consts, Exists, ForAll, If, Implies, Int, Ints, RealVal, Reals
from kdrag.theories.real import (
    RSeq,
    abs,
    abs_add,
    abs_div,
    abs_mul,
    abs_neg,
    abs_pos,
    abs_pos_iff,
    abs_triangle,
    min,
)
from kdrag.theories.real.seq import add, div, has_lim, mul, smul


a, b = Consts("a b", RSeq)
x, y, c = Reals("x y c")
u, v, w, z = Reals("u v w z")
n = Int("n")


@Theorem(ForAll([a, y], has_lim(a, y), ForAll(n, n >= 0, a[n] >= 0), y >= 0))
def lim_of_nonneg_seq(l):
    a, y = l.fixes()
    limit, nonneg = l.intros(), l.intros()
    l.unfold(has_lim, at=limit)
    l.contra()
    positive = l.have(-y > 0, by=[])
    cutoff = l.obtain(l.specialize(0, -y, positive))
    m = cutoff + 1
    l.specialize(nonneg, m)
    l.auto(by=[abs.defn(a[m] - y)])


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
    l.have(eta > 0, by=[abs_pos(c)])
    ha = l.specialize(ha, eta)
    bound, n = Ints("N n")
    witness = l.have(
        Exists(bound, bound >= 0, ForAll(n, n > bound, abs(a[n] - x) < eta)), by=[]
    )
    l.clear(ha)
    N = l.obtain(witness)
    l.exists(N)
    l.split()
    l.auto()
    m = l.fix()
    l.intros()
    l.have(abs(a[m] - x) < eta, by=[])
    l.have(abs(c) * eta < eps, by=[abs_pos(c)])
    l.have(c * a[m] - c * x == c * (a[m] - x), by=[])
    l.auto(by=[smul.defn(c, a), abs_mul(c, a[m] - x), abs_pos(c)])


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
    ha, hb = l.intros(), l.intros()
    eps = l.fix()
    l.intros()
    # Each sequence contributes half the error budget.
    ha = l.specialize(ha, eps / 2)
    hb = l.specialize(hb, eps / 2)
    bound, n = Ints("N n")
    tail_a = l.have(
        Exists(bound, bound >= 0, ForAll(n, n > bound, abs(a[n] - x) < eps / 2)), by=[]
    )
    l.clear(ha)
    N1 = l.obtain(tail_a)
    tail_b = l.have(
        Exists(bound, bound >= 0, ForAll(n, n > bound, abs(b[n] - y) < eps / 2)), by=[]
    )
    l.clear(hb)
    N2 = l.obtain(tail_b)
    l.exists(If(N1 > N2, N1, N2))
    l.split()
    l.auto()
    m = l.fix()
    l.intros()
    l.have(abs(a[m] - x) < eps / 2, by=[])
    l.have(abs(b[m] - y) < eps / 2, by=[])
    l.have(
        abs((a[m] + b[m]) - (x + y)) <= abs(a[m] - x) + abs(b[m] - y),
        by=[abs_add(a[m] - x, b[m] - y)],
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
    ha, hb = l.intros(), l.intros()
    eps = l.fix()
    l.intros()
    # Keep both errors below one and small enough for the product estimate.
    eta = min(1, eps / (2 * (abs(x) + abs(y) + 1)))
    l.have(eta > 0, by=[abs_pos(x), abs_pos(y), min.defn])
    ha = l.specialize(ha, eta)
    hb = l.specialize(hb, eta)
    bound, n = Ints("N n")
    tail_a = l.have(
        Exists(bound, bound >= 0, ForAll(n, n > bound, abs(a[n] - x) < eta)), by=[]
    )
    l.clear(ha)
    N1 = l.obtain(tail_a)
    tail_b = l.have(
        Exists(bound, bound >= 0, ForAll(n, n > bound, abs(b[n] - y) < eta)), by=[]
    )
    l.clear(hb)
    N2 = l.obtain(tail_b)
    l.exists(If(N1 > N2, N1, N2))
    l.split()
    l.auto()
    m = l.fix()
    l.intros()
    l.have(abs(a[m] - x) < eta, by=[])
    l.have(abs(b[m] - y) < eta, by=[])
    l.have(
        And(eta <= 1, 2 * eta * (abs(x) + abs(y) + 1) <= eps),
        by=[abs_pos(x), abs_pos(y), min.defn],
    )
    u, v = a[m] - x, b[m] - y
    da, db = abs(u), abs(v)
    error_bound = da * db + abs(y) * da + abs(x) * db
    l.have(a[m] * b[m] - x * y == u * v + y * u + x * v, by=[])
    l.have(
        abs(a[m] * b[m] - x * y) <= error_bound,
        by=[
            abs_add(u * v + y * u, x * v),
            abs_add(u * v, y * u),
            abs_mul(u, v),
            abs_mul(y, u),
            abs_mul(x, v),
        ],
    )
    l.have(error_bound < eps, by=[abs_pos(u), abs_pos(v), abs_pos(x), abs_pos(y)])
    l.auto(by=[mul.defn(a, b)])


@Theorem(
    ForAll(
        [u, v, w, z],
        And(v != 0, z != 0),
        (u / v) + -1 * (w / z) == (u - w) / v + w * ((z - v) / (v * z)),
    )
)
def div_decomp(l):
    u, v, w, z = l.fixes()
    l.intros()
    l.auto()


@Theorem(
    ForAll([a, b, x, y], has_lim(a, x), has_lim(b, y), y != 0, has_lim(a / b, x / y))
)
def has_lim_div(l):
    a, b, x, y = l.fixes()
    l.unfold(has_lim)
    ha, hb = l.intros(), l.intros()
    l.intros()
    eps = l.fix()
    l.intros()
    # Keep the denominator away from zero and split the quotient error.
    Y, X = abs(y), abs(x)
    ea = eps * Y / 4
    eb = min(Y / 2, eps * Y * Y / (4 * (X + 1)))
    l.have(Y > 0, by=[abs_pos_iff(y)])
    l.have(ea > 0, by=[])
    l.have(eb > 0, by=[abs_pos(x), min.defn])
    ha = l.specialize(ha, ea)
    hb = l.specialize(hb, eb)
    bound, n = Ints("N n")
    tail_a = l.have(
        Exists(bound, bound >= 0, ForAll(n, n > bound, abs(a[n] - x) < ea)), by=[]
    )
    l.clear(ha)
    N1 = l.obtain(tail_a)
    tail_b = l.have(
        Exists(bound, bound >= 0, ForAll(n, n > bound, abs(b[n] - y) < eb)), by=[]
    )
    l.clear(hb)
    N2 = l.obtain(tail_b)
    l.exists(If(N1 > N2, N1, N2))
    l.split()
    l.auto()
    l.unfold(div)
    l.beta()
    m = l.fix()
    l.intros()

    am, bm = a[m], b[m]
    da, db, B = abs(am - x), abs(bm - y), abs(bm)
    l.have(da < ea, by=[])
    l.have(db < eb, by=[])
    l.have(And(db < Y / 2, db * (4 * (X + 1)) < eps * Y * Y), by=[min.defn, abs_pos(x)])
    l.have(abs(y - bm) == db, by=[abs_neg(bm - y)])
    l.have(Y <= db + B, by=[abs_triangle(y, RealVal(0), bm)])
    l.have(B > Y / 2, by=[])
    l.have(bm != 0, by=[abs_pos_iff(bm)])
    t1 = (am - x) / bm
    t2 = x * ((y - bm) / (bm * y))
    decomp = l.have(am / bm - x / y == t1 + t2, by=[div_decomp(am, bm, x, y)])
    l.have(abs(t1) == da / B, by=[abs_div(am - x, bm)])
    l.have(
        abs(t2) == X * (db / (B * Y)),
        by=[abs_mul(x, (y - bm) / (bm * y)), abs_div(y - bm, bm * y), abs_mul(bm, y)],
    )
    l.have(da / B < eps / 2, by=[])
    l.have(X * (db / (B * Y)) < eps / 2, by=[abs_pos(x), abs_pos(bm - y)])
    bound = l.have(abs(t1 + t2) < eps, by=[abs_add(t1, t2)])
    # Discharge congruence with just the equality and the scalar bound.
    result = abs(am / bm - x / y) < eps
    l.auto(by=[prove(Implies(And(decomp, bound), result))])
