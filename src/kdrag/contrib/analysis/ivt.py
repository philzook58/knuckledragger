"""The intermediate value theorem by bisection and nested intervals."""

from kdrag import Struct, Theorem, define
from kdrag.smt import (
    And,
    ArraySort,
    Const,
    Consts,
    Eq,
    Exists,
    ForAll,
    If,
    IntSort,
    Lambda,
    Or,
    Reals,
    ToReal,
)
import kdrag.theories.int as int_
import kdrag.theories.real as real
from kdrag.theories.real import rset
from kdrag.theories.real.rseq import n

from ._int_recursion import int_recursion
from .cont import cont_on, cont_within_at

_Bracket = Struct("analysis.Bracket", ("left", real.R), ("right", real.R))
bracket = Const("bracket", _Bracket)
brackets = Const("brackets", ArraySort(IntSort(), _Bracket))
f = Const("f", real.RFun)
lo, hi, level, x = Reals("lo hi level x")
a, b = Consts("a b", real.RSeq)


def _straddles(f, level, lo, hi):
    return Or(And(f[lo] < level, level <= f[hi]), And(f[hi] < level, level <= f[lo]))


mid = (bracket.left + bracket.right) / 2
# Keep the left half exactly when its endpoints straddle the level.
_bisect = define(
    "analysis.bisect",
    [f, level, bracket],
    If(
        Eq(f[bracket.left] < level, level <= f[mid]),
        _Bracket.mk(bracket.left, mid),
        _Bracket.mk(mid, bracket.right),
    ),
)

_next = _bisect(f, level, bracket)


@Theorem(
    ForAll(
        [f, level, bracket],
        bracket.left <= bracket.right,
        _straddles(f, level, bracket.left, bracket.right),
        And(
            bracket.left <= _next.left,
            _next.left <= _next.right,
            _next.right <= bracket.right,
            _straddles(f, level, _next.left, _next.right),
            _next.right - _next.left == (bracket.right - bracket.left) / 2,
        ),
    )
)
def _bisect_step(l):
    f, level, bracket = l.fixes()
    l.intros()
    l.auto(by=[_bisect.defn(f, level, bracket)])


def _bounds(f, lo, hi, level, a, b, n):
    return And(
        lo <= a,
        a <= b,
        b <= hi,
        _straddles(f, level, a, b),
        (b - a) * (ToReal(n) + 1) <= hi - lo,
    )


def _recurrence(f, level, brackets):
    return ForAll(n, n >= 0, brackets[n + 1] == _bisect(f, level, brackets[n]))


@Theorem(
    ForAll(
        [f, lo, hi, level, brackets],
        lo < hi,
        _straddles(f, level, lo, hi),
        brackets[0] == _Bracket.mk(lo, hi),
        _recurrence(f, level, brackets),
        ForAll(
            n, n >= 0, _bounds(f, lo, hi, level, brackets[n].left, brackets[n].right, n)
        ),
    )
)
def _bisection_invariant(l):
    f, lo, hi, level, brackets = l.fixes()
    *_, recurrence = l.intros()
    n = l.fix()
    l.intro()
    l.induct(n, using=int_.induct_nat)
    l.auto()
    j = l.fix()
    l.intros()
    l.specialize(recurrence, j)
    # Halving the width gives a reciprocal bound without introducing powers.
    l.auto(by=[_bisect_step(f, level, brackets[j])])


def _intervals(a, b):
    i = rset.i
    return Lambda(i, real.icc(a[i], b[i]))


def _all_bounds(f, lo, hi, level, a, b):
    return ForAll(n, n >= 0, _bounds(f, lo, hi, level, a[n], b[n], n))


@Theorem(
    ForAll(
        [f, lo, hi, level],
        lo < hi,
        _straddles(f, level, lo, hi),
        Exists(
            [a, b],
            And(rset.nested(_intervals(a, b)), _all_bounds(f, lo, hi, level, a, b)),
        ),
    )
)
def _exists_nested_bisection(l):
    f, lo, hi, level = l.fixes()
    l.intros()
    step = Lambda([n, bracket], _bisect(f, level, bracket))
    brackets, facts = l.obtain(
        l.specialize(int_recursion(_Bracket), step, _Bracket.mk(lo, hi))
    )
    initial, steps = l.andE(facts)
    l.specialize(initial, 0)
    recurrence = l.have(_recurrence(f, level, brackets), by=[])
    l.clear(steps)
    a, b = Lambda(n, brackets[n].left), Lambda(n, brackets[n].right)
    bounds = l.have(
        _all_bounds(f, lo, hi, level, a, b),
        by=[_bisection_invariant(f, lo, hi, level, brackets)],
    )
    l.exists(a, b)
    l.split()
    l.unfold(rset.nested)
    l.beta()
    j = l.fix()
    l.intro()
    l.specialize(bounds, j)
    l.specialize(recurrence, j)
    current, following = brackets[j], brackets[j + 1]
    l.auto(
        by=[
            _bisect_step(f, level, current),
            rset.icc_subset_icc_iff(
                following.left, following.right, current.left, current.right
            ),
        ]
    )
    l.auto()


def _in_every_bracket(a, b, x):
    return ForAll(n, n >= 0, _intervals(a, b)[n][x])


@Theorem(
    ForAll(
        [f, lo, hi, level, a, b, x],
        lo < hi,
        cont_on(f, real.icc(lo, hi)),
        _all_bounds(f, lo, hi, level, a, b),
        _in_every_bracket(a, b, x),
        f[x] == level,
    )
)
def _level_of_mem_every_bracket(l):
    f, lo, hi, level, a, b, c = l.fixes()
    _, _, bounds, inside = l.intros()
    l.specialize(inside, 0, keep=True)
    l.specialize(bounds, 0, keep=True)
    domain = real.icc(lo, hi)
    l.have(domain[c], by=[real.icc.defn(lo, hi), real.icc.defn(a[0], b[0])])
    l.have(cont_within_at(f, domain, c), by=[cont_on.defn(f, domain)])
    l.contra()
    # A sufficiently short bracket puts both endpoint values within this error.
    eps = real.abs(f[c] - level)
    positive = l.have(eps > 0, by=[real.abs.defn(f[c] - level)])
    unfolded = l.have(
        cont_within_at.defn(f, domain, c).thm.arg(1),
        by=[cont_within_at.defn(f, domain, c)],
    )
    radius, near = l.obtain(l.specialize(unfolded, eps, positive))
    _, close = l.andE(near)
    big = l.have(
        Exists(n, hi - lo < radius * ToReal(n)), by=[real.archimedes(radius, hi - lo)]
    )
    j, _ = l.obtain(big)
    l.have(j >= 0, by=[])
    l.specialize(inside, j)
    l.specialize(bounds, j)
    l.have(b[j] - a[j] < radius, by=[])
    l.have(
        And(
            domain[a[j]],
            domain[b[j]],
            real.abs(c - a[j]) < radius,
            real.abs(c - b[j]) < radius,
        ),
        by=[
            real.icc.defn(lo, hi),
            real.icc.defn(a[j], b[j]),
            real.abs.defn(c - a[j]),
            real.abs.defn(c - b[j]),
        ],
    )
    l.specialize(close, a[j], keep=True)
    l.specialize(close, b[j])
    l.auto(
        by=[
            real.abs.defn(f[c] - level),
            real.abs.defn(f[c] - f[a[j]]),
            real.abs.defn(f[c] - f[b[j]]),
        ]
    )


@Theorem(
    ForAll(
        [f, lo, hi, level],
        lo < hi,
        cont_on(f, real.icc(lo, hi)),
        Or(And(f[lo] < level, level < f[hi]), And(f[hi] < level, level < f[lo])),
        Exists(x, lo < x, x < hi, f[x] == level),
    )
)
def intermediate_value_of_nested_intervals(l):
    """Abbott 4.5.1, using the nested interval proof on p. 138."""
    f, lo, hi, level = l.fixes()
    ordered, _, _ = l.intros()
    straddles = l.have(_straddles(f, level, lo, hi), by=[])
    (a, b), witness = l.obtain(
        l.specialize(_exists_nested_bisection, f, lo, hi, level, ordered, straddles)
    )
    nested, bounds = l.andE(witness)
    ordered = l.have(ForAll(n, n >= 0, a[n] <= b[n]), by=[])
    c, _ = l.obtain(
        l.specialize(rset.nonempty_iinter_icc_of_nested, a, b, nested, ordered)
    )
    inside = l.have(_in_every_bracket(a, b, c), by=[real.iinter.defn(_intervals(a, b))])
    l.have(f[c] == level, by=[_level_of_mem_every_bracket(f, lo, hi, level, a, b, c)])
    l.specialize(inside, 0)
    l.specialize(bounds, 0)
    l.exists(c)
    l.auto(by=[real.icc.defn(a[0], b[0])])
