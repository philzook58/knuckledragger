"""Bounds, completeness, and operations on sets of real numbers."""

from kdrag import QForAll, Theorem, axiom, define, prove
from kdrag.smt import (
    And,
    Const,
    Consts,
    Exists,
    ForAll,
    IntSort,
    Lambda,
    Reals,
)
from kdrag.theories.real import RSet, RSetSeq

x, y, z, M, c, u, v = Reals("x y z M c u v")
A, B, C = Consts("A B C", RSet)

is_ub = define("RSet.is_ub", [A, u], ForAll(x, A[x], x <= u))
is_lb = define("RSet.is_lb", [A, u], ForAll(x, A[x], u <= x))

upper_bounds = define("RSet.upper_bounds", A, Lambda(u, is_ub(A, u)))
lower_bounds = define("RSet.lower_bounds", A, Lambda(u, is_lb(A, u)))


bdd_above = define("RSet.bdd_above", A, Exists(u, is_ub(A, u)))
bdd_below = define("RSet.bdd_below", A, Exists(u, is_lb(A, u)))
is_lub = define(
    "RSet.is_lub",
    [A, u],
    And(is_ub(A, u), ForAll(v, is_ub(A, v), u <= v)),
)
is_glb = define(
    "RSet.is_glb",
    [A, u],
    And(is_lb(A, u), ForAll(v, is_lb(A, v), v <= u)),
)

exists_is_lub_of_bdd_above = axiom(
    ForAll(A, Exists(x, A[x]), bdd_above(A), Exists(u, is_lub(A, u)))
)


@Theorem(ForAll([A, u], is_lb(-A, u) == is_ub(A, -u)))
def is_lb_neg(l):
    A, u = l.fixes()
    l.unfold(is_lb, is_ub)
    l.split()
    h = l.intro()
    x = l.fix()
    l.specialize(h, -x)
    l.auto()
    h = l.intro()
    x = l.fix()
    l.specialize(h, -x)
    l.auto()


@Theorem(ForAll([A, u], is_ub(-A, u) == is_lb(A, -u)))
def is_ub_neg(l):
    A, u = l.fixes()
    # Prove this direction directly to avoid matching through double images.
    l.unfold(is_lb, is_ub)
    l.split()
    h = l.intro()
    x = l.fix()
    l.specialize(h, -x)
    l.auto()
    h = l.intro()
    x = l.fix()
    l.specialize(h, -x)
    l.auto()


@Theorem(ForAll(A, bdd_below(-A), bdd_above(A)))
def bdd_above_of_bdd_below_neg(l):
    A = l.fix()
    l.unfold(bdd_above, bdd_below)
    h = l.intro()
    b = l.obtain(h)
    l.exists(-b)
    l.auto(by=[is_lb_neg(A, b)])


@Theorem(ForAll(A, bdd_above(-A), bdd_below(A)))
def bdd_below_of_bdd_above_neg(l):
    A = l.fix()
    l.unfold(bdd_above, bdd_below)
    h = l.intro()
    b = l.obtain(h)
    l.exists(-b)
    l.auto(by=[is_ub_neg(A, b)])


@Theorem(ForAll(A, bdd_above(-A) == bdd_below(A)))
def bdd_above_neg(l):
    A = l.fix()
    l.unfold(bdd_above, bdd_below)
    l.split()
    h = l.intro()
    b = l.obtain(h)
    l.exists(-b)
    l.auto(by=[is_ub_neg(A, b)])
    h = l.intro()
    b = l.obtain(h)
    # A lower bound b of A gives an upper bound -b of its image under negation.
    l.exists(-b)
    l.auto(by=[is_ub_neg(A, -b)])


@Theorem(ForAll([A, x], is_glb(-A, -x), is_lub(A, x)))
def is_lub_of_is_glb_neg(l):
    A, x = l.fixes()
    l.unfold(is_glb, is_lub)
    l.intro()
    l.split()

    l.auto(by=[is_lb_neg(A, -x)])

    v = l.fix()
    l.intro()
    l.have(is_lb(-A, -v), by=[is_lb_neg(A, -v)])
    l.auto()


@Theorem(ForAll([A, x], is_lub(-A, -x), is_glb(A, x)))
def is_glb_of_is_lub_neg(l):
    A, x = l.fixes()
    l.unfold(is_glb, is_lub)
    l.intro()
    l.split()

    l.auto(by=[is_ub_neg(A, -x)])

    v = l.fix()
    l.intro()
    l.have(is_ub(-A, -v), by=[is_ub_neg(A, -v)])
    l.auto()


@Theorem(ForAll(A, Exists(x, A[x]), bdd_below(A), Exists(u, is_glb(A, u))))
def exists_is_glb_of_bdd_below(l):
    A = l.fix()
    l.intro()
    l.intro()
    l.have(bdd_above(-A), by=[bdd_above_neg(A)])
    l.have(Exists(x, (-A)[x]), by=[])
    h = l.have(Exists(u, is_lub(-A, u)), by=[exists_is_lub_of_bdd_above(-A)])
    lub = l.obtain(h)
    l.exists(-lub)
    l.auto(by=[is_glb_of_is_lub_neg(A, -lub)])


lb_le_ub = prove(
    ForAll([A, x, y, z], A[x], is_lb(A, y), is_ub(A, z), y <= z),
    by=[is_lb.defn, is_ub.defn],
)


shift = define(
    "shift",
    [A, c],
    Lambda([x], A[x - c]),
)

sing = define(
    "RSet.sing",
    [c],
    Lambda([x], x == c),
)
sing_elem = prove(
    QForAll([c, x], sing(c)[x] == (x == c)),
    by=[sing.defn],
)


An = Const("An", RSetSeq)
n = Const("n", IntSort())

nested = define("nested", [An], ForAll(n, n >= 0, An[n + 1] <= An[n]))
