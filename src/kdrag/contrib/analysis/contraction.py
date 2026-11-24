"""The contraction mapping theorem on the real line."""

from kdrag import Theorem, define
from kdrag.datatype import define_fun
from kdrag.smt import And, Const, Exists, ForAll, Function, If, IntVal, Lambda, Reals
import kdrag.theories.nat as nat
import kdrag.theories.real as real
from kdrag.theories.real.rseq import (
    a,
    cumsum,
    diff,
    f,
    finsum,
    has_lim,
    is_cauchy,
    is_summable,
    m,
    n,
)

from .cauchy import is_cauchy_iff_exists_has_lim
from .finsum import finsum_diff
from .series import exists_has_sum_of_geometric_decay, is_summable_iff_is_cauchy_cumsum

c, x, y, p = Reals("c x y p")

is_contraction = define(
    "analysis.is_contraction",
    [f, c],
    And(c >= 0, c < 1, ForAll([x, y], real.abs(f[x] - f[y]) <= c * real.abs(x - y))),
)

k = Const("k", nat.Nat)
_iterate = Function("analysis.iterate_nat", nat.Nat, real.RFun, real.R, real.R)
_iterate = define_fun(
    [
        _iterate(nat.Z, f, x) == x,
        _iterate(nat.S(k), f, x) == f[_iterate(k, f, x)],
    ]
)
orbit = define("analysis.orbit", [f, x], Lambda(n, _iterate(nat.from_int(n), f, x)))


@Theorem(ForAll([f, x], orbit(f, x)[0] == x))
def orbit_zero(l):
    f, x = l.fixes()
    l.auto(by=[orbit.defn(f, x), nat.from_int.defn(0), _iterate.case0(f, x)])


@Theorem(ForAll([f, x], ForAll(n, n >= 0, orbit(f, x)[n + 1] == f[orbit(f, x)[n]])))
def orbit_succ(l):
    f, x = l.fixes()
    n = l.fix()
    l.intro()
    l.auto(
        by=[
            orbit.defn(f, x),
            nat.from_int.defn(n + 1),
            _iterate.case1(nat.from_int(n), f, x),
        ]
    )


@Theorem(ForAll([f, c], is_contraction(f, c), real.is_cont(f)))
def is_cont_of_is_contraction(l):
    f, c = l.fixes()
    l.unfold(is_contraction, real.is_cont)
    _, _, contract = l.andE(l.intro())
    l.unfold(real.cont_at)
    x = l.fix()
    eps = l.fix()
    l.intro()
    # The same radius works because the Lipschitz constant is below one.
    l.exists(eps)
    l.split()
    l.auto()
    y = l.fix()
    l.intro()
    l.specialize(contract, x, y)
    l.auto(by=[real.abs_pos(x - y)])


@Theorem(
    ForAll(
        [f, c, a],
        is_contraction(f, c),
        ForAll(n, n >= 0, a[n + 1] == f[a[n]]),
        is_summable(diff(a)),
    )
)
def is_summable_diff_of_contraction_orbit(l):
    f, c, a = l.fixes()
    l.unfold(is_contraction)
    contraction, step = l.intros()
    nonneg, small, contract = l.andE(contraction)
    d = diff(a)
    # The increments are geometrically dominated, so their series converges.
    decay = l.have(ForAll(m, m >= 0, real.abs(d[m + 1]) <= c * real.abs(d[m])))
    j = l.fix()
    after_zero = l.intro()
    next_after_zero = l.have(j + 1 >= 0, by=[])
    l.specialize(step, j, after_zero, keep=True)
    l.specialize(step, j + 1, next_after_zero)
    l.specialize(contract, a[j + 1], a[j])
    l.auto(by=[diff.defn(a)])
    value, _ = l.obtain(
        l.specialize(exists_has_sum_of_geometric_decay, d, c, 0, nonneg, small, decay)
    )
    l.unfold(is_summable)
    l.exists(value)
    l.auto()


@Theorem(ForAll(a, is_cauchy(cumsum(diff(a))), is_cauchy(a)))
def _is_cauchy_of_is_cauchy_cumsum_diff(l):
    a = l.fix()
    d = diff(a)
    l.unfold(is_cauchy)
    tails = l.intro()
    eps = l.fix()
    positive = l.intro()
    N, close = l.obtain(l.specialize(tails, eps, positive))
    l.exists(N)
    j, k = l.fixes()
    l.intros()
    l.specialize(close, j, k)
    # Telescoping cancels the common initial value a[0].
    l.auto(
        by=[finsum.defn(d, j), finsum_diff(a, j), finsum.defn(d, k), finsum_diff(a, k)]
    )


@Theorem(
    ForAll(
        [f, c, a],
        is_contraction(f, c),
        ForAll(n, n >= 0, a[n + 1] == f[a[n]]),
        is_cauchy(a),
    )
)
def is_cauchy_of_contraction_orbit(l):
    f, c, a = l.fixes()
    l.intros()
    d = diff(a)
    l.have(is_summable(d), by=[is_summable_diff_of_contraction_orbit(f, c, a)])
    l.auto(
        by=[is_summable_iff_is_cauchy_cumsum(d), _is_cauchy_of_is_cauchy_cumsum_diff(a)]
    )


@Theorem(
    ForAll(
        [f, c, a, p],
        is_contraction(f, c),
        ForAll(n, n >= 0, a[n + 1] == f[a[n]]),
        has_lim(a, p),
        f[p] == p,
    )
)
def fixed_of_has_lim_contraction_orbit(l):
    f, c, a, p = l.fixes()
    l.unfold(is_contraction, has_lim)
    contraction, step, tends = l.intros()
    _, _, contract = l.andE(contraction)
    distance = real.abs(f[p] - p)
    l.contra()
    positive = l.have(distance / 2 > 0, by=[real.abs_pos_iff(f[p] - p)])
    N, close = l.obtain(l.specialize(tends, distance / 2, positive))
    j = If(N < 0, IntVal(0), N + 1)
    index_nonneg = l.have(j >= 0, by=[])
    l.specialize(step, j, index_nonneg)
    l.specialize(close, j, keep=True)
    l.specialize(close, j + 1)
    l.specialize(contract, p, a[j])
    # Estimate |f(p) - p| through f(a[j]) = a[j+1].
    l.auto(
        by=[
            real.abs_triangle(f[p], p, f[a[j]]),
            real.abs_neg(a[j] - p),
            real.abs_pos(p - a[j]),
        ]
    )


@Theorem(ForAll([f, c, x, y], is_contraction(f, c), f[x] == x, f[y] == y, x == y))
def contraction_fixed_unique(l):
    f, c, x, y = l.fixes()
    l.unfold(is_contraction)
    contraction, _, _ = l.intros()
    _, _, contract = l.andE(contraction)
    l.specialize(contract, x, y)
    l.auto(by=[real.abs_pos_iff(x - y), real.abs_pos(x - y)])


@Theorem(
    ForAll(
        [f, c, x],
        is_contraction(f, c),
        Exists(p, And(f[p] == p, has_lim(orbit(f, x), p))),
    )
)
def exists_fixed_limit_of_contraction(l):
    f, c, x = l.fixes()
    l.intro()
    a = orbit(f, x)
    l.have(ForAll(n, n >= 0, a[n + 1] == f[a[n]]), by=[orbit_succ(f, x)])
    l.have(is_cauchy(a), by=[is_cauchy_of_contraction_orbit(f, c, a)])
    limit = l.have(Exists(p, has_lim(a, p)), by=[is_cauchy_iff_exists_has_lim(a)])
    fixed, _ = l.obtain(limit)
    l.exists(fixed)
    l.auto(by=[fixed_of_has_lim_contraction_orbit(f, c, a, fixed)])


@Theorem(
    ForAll(
        [f, c],
        is_contraction(f, c),
        Exists(
            p,
            And(
                f[p] == p,
                ForAll(x, f[x] == x, x == p),
                ForAll(x, has_lim(orbit(f, x), p)),
            ),
        ),
    )
)
def contraction_mapping(l):
    """A contraction on the real line has one fixed point, attracting every orbit."""
    f, c = l.fixes()
    contract = l.intro()
    p, witness = l.obtain(
        l.specialize(exists_fixed_limit_of_contraction, f, c, 0, contract)
    )
    fixed, _ = l.andE(witness)
    l.exists(p)
    l.split()
    l.auto()
    x = l.fix()
    l.intro()
    l.auto(by=[contraction_fixed_unique(f, c, x, p)])
    x = l.fix()
    q, witness = l.obtain(
        l.specialize(exists_fixed_limit_of_contraction, f, c, x, contract)
    )
    l.auto(by=[contraction_fixed_unique(f, c, q, p)])
