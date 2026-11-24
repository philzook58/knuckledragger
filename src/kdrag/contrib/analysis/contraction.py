"""The contraction mapping theorem on the real line."""

import kdrag as kd
from kdrag import Theorem, define
from kdrag.smt import And, Exists, ForAll, Lambda, Reals
import kdrag.theories.real as real
from kdrag.theories.real.cont import cont_at_of_is_cont
from kdrag.theories.real.rseq import (
    a,
    diff,
    f,
    has_lim,
    is_cauchy,
    is_summable,
    lim_unique,
    m,
    n,
    shift,
)

from ._int_recursion import int_recursion
from .cauchy import is_cauchy_iff_exists_has_lim
from .cont import has_lim_comp_of_cont_at
from .rseq import has_lim_congr_nonneg, has_lim_shift
from .series import exists_has_sum_of_geometric_decay, is_cauchy_of_is_summable_diff

c, x, y, p = Reals("c x y p")

is_contraction = define(
    "analysis.is_contraction",
    [f, c],
    And(c >= 0, c < 1, ForAll([x, y], real.abs(f[x] - f[y]) <= c * real.abs(x - y))),
)

(_iterate,), _iterate_spec = kd.kernel.choose(int_recursion(real.R))


def _orbit_step(f):
    return Lambda([n, y], f[y])


orbit = define("analysis.orbit", [f, x], _iterate(_orbit_step(f), x))


@Theorem(ForAll([f, x], orbit(f, x)[0] == x))
def orbit_zero(l):
    f, x = l.fixes()
    initial, _ = l.andE(l.specialize(_iterate_spec, _orbit_step(f), x))
    l.specialize(initial, 0)
    l.auto(by=[orbit.defn(f, x)])


@Theorem(ForAll([f, x], ForAll(n, n >= 0, orbit(f, x)[n + 1] == f[orbit(f, x)[n]])))
def orbit_succ(l):
    f, x = l.fixes()
    n = l.fix()
    l.intro()
    _, recurrence = l.andE(l.specialize(_iterate_spec, _orbit_step(f), x))
    l.specialize(recurrence, n)
    l.auto(by=[orbit.defn(f, x)])


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
    l.auto(
        by=[
            is_summable_diff_of_contraction_orbit(f, c, a),
            is_cauchy_of_is_summable_diff(a),
        ]
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
    l.intros()
    shifted = shift(a, -1)
    image = Lambda(n, f[a[n]])
    l.have(
        real.cont_at(f, p),
        by=[is_cont_of_is_contraction(f, c), cont_at_of_is_cont(f, p)],
    )
    l.have(has_lim(image, f[p]), by=[has_lim_comp_of_cont_at(a, f, p)])
    # The image of the orbit agrees with the shifted orbit at nonnegative indices.
    l.have(ForAll(n, n >= 0, image[n] == shifted[n]), by=[shift.defn(a, -1)])
    l.have(has_lim(shifted, f[p]), by=[has_lim_congr_nonneg(image, shifted, f[p])])
    l.have(has_lim(shifted, p), by=[has_lim_shift(a, p, -1)])
    l.auto(by=[lim_unique(shifted, f[p], p)])


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
    l.andE(witness)
    l.exists(p)
    l.split()
    l.auto()
    x = l.fix()
    l.intro()
    l.auto(by=[contraction_fixed_unique(f, c, x, p)])
    x = l.fix()
    q, _ = l.obtain(l.specialize(exists_fixed_limit_of_contraction, f, c, x, contract))
    l.auto(by=[contraction_fixed_unique(f, c, q, p)])
