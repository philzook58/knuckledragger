"""Bounds, completeness, and operations on sets of real numbers."""

from kdrag import QForAll, Theorem, axiom, define, prove
from kdrag.smt import (
    And,
    Const,
    Consts,
    Eq,
    Exists,
    ForAll,
    Ints,
    If,
    Lambda,
    Reals,
)
from kdrag.theories.real import RSet, RSetSeq, RSeq, icc, iinter

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


le_of_mem_of_is_ub = prove(
    ForAll([A, x, u], A[x], is_ub(A, u), x <= u), by=[is_ub.defn]
)

is_ub_of_is_lub = prove(
    ForAll([A, u], is_lub(A, u), is_ub(A, u)), by=[is_lub.defn]
)

le_of_is_lub_of_is_ub = prove(
    ForAll([A, u, v], is_lub(A, u), is_ub(A, v), u <= v), by=[is_lub.defn]
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
n, m, i = Ints("n m i")

nested = define("nested", [An], ForAll(n, n >= 0, An[n + 1] <= An[n]))


@Theorem(ForAll([x, y], Eq(Exists(z, icc(x, y)[z]), x <= y)))
def nonempty_icc(l):
    l.fixes()
    l.unfold(icc)
    l.auto()


@Theorem(
    ForAll([x, y, u, v], x <= y,
           Eq(icc(x, y) <= icc(u, v), And(u <= x, y <= v)))
)
def icc_subset_icc_iff(l):
    l.fixes()
    l.intro()
    l.unfold(icc)
    l.auto()


@Theorem(ForAll([x, y], is_ub(icc(x, y), y)))
def is_ub_icc(l):
    l.fixes()
    l.unfold(is_ub, icc)
    l.auto()


@Theorem(ForAll([x, y], is_lb(icc(x, y), x)))
def is_lb_icc(l):
    l.fixes()
    l.unfold(is_lb, icc)
    l.auto()


@Theorem(ForAll([x, y], x <= y, is_lub(icc(x, y), y)))
def is_lub_icc(l):
    x, y = l.fixes()
    l.unfold(is_lub)
    l.intro()
    l.split()
    l.auto(by=[is_ub_icc(x, y)])
    l.unfold(is_ub, icc)
    l.auto()


@Theorem(ForAll([An, n, m], nested(An), n >= 0, n <= m, An[m] <= An[n]))
def nested_subset(l):
    from kdrag.theories.int import induct_strong

    An, n, m = l.fixes()
    l.unfold(nested)
    steps = l.intro()
    l.intro()
    # Keep n <= m in the predicate so indices below n give vacuous cases.
    l.induct(m, using=induct_strong)
    k = l.fix()
    ih = l.intro()
    l.intro()
    l.cases(k == n, k > n)
    l.auto()
    # For k > n >= 0, the predecessor is smaller in absolute value.
    l.specialize(ih, k - 1)
    l.specialize(steps, k - 1)
    l.auto()


a, b = Consts("a b", RSeq)
I = Lambda(i, icc(a[i], b[i]))


@Theorem(
    ForAll([a, b], nested(I),
           ForAll(n, n >= 0, a[n] <= b[n]),
           ForAll([n, m], n >= 0, m >= 0, a[n] <= b[m]))
)
def nested_icc_bounds(l):
    a, b = l.fixes()
    _, nonempty = l.intros()
    n, m = l.fixes()
    l.intros()
    intervals = Lambda(i, icc(a[i], b[i]))
    # The nonempty interval at max(n,m) is contained in both earlier intervals.
    k = If(n <= m, m, n)
    l.specialize(nonempty, k)
    l.have(a[k] <= b[k], by=[])
    l.have(intervals(k) <= intervals(n), by=[nested_subset(intervals, n, k)])
    l.have(intervals(k) <= intervals(m), by=[nested_subset(intervals, m, k)])
    l.auto(by=[icc_subset_icc_iff(a[k], b[k], a[n], b[n]),
               icc_subset_icc_iff(a[k], b[k], a[m], b[m])])


@Theorem(
    ForAll([a, b], ForAll([n, m], n >= 0, m >= 0, a[n] <= b[m]),
           Exists(x, ForAll(n, n >= 0, And(a[n] <= x, x <= b[n]))))
)
def exists_between_seq(l):
    """Uniformly separated real sequences admit a common interpolant."""
    a, b = l.fixes()
    cross_bounds = l.intro()
    # Ignore negative indices. Every upper-sequence term bounds this range.
    lower = Lambda(x, Exists(n, n >= 0, a[n] == x))
    bounds = l.have(ForAll(m, m >= 0, is_ub(lower, b[m])))
    j = l.fix()
    l.intro()
    l.unfold(is_ub)
    point = l.fix()
    l.beta()
    member = l.intro()
    k = l.obtain(member)
    l.specialize(cross_bounds, k, j)
    l.auto()

    # Take the supremum of the lower sequence, bounded by b[0].
    l.have(lower[a[0]], by=[])
    l.have(Exists(x, lower[x]), by=[])
    l.specialize(bounds, 0, keep=True)
    l.have(bdd_above(lower), by=[bdd_above.defn(lower)])
    supremum = l.have(
        Exists(u, is_lub(lower, u)), by=[exists_is_lub_of_bdd_above(lower)]
    )
    s = l.obtain(supremum)
    l.exists(s)
    j = l.fix()
    l.intro()
    l.specialize(bounds, j)
    # Membership gives the lower inequality; leastness gives the upper one.
    l.have(lower[a[j]], by=[])
    l.have(is_ub(lower, s), by=[is_ub_of_is_lub(lower, s)])
    l.have(a[j] <= s, by=[le_of_mem_of_is_ub(lower, a[j], s)])
    l.auto(by=[le_of_is_lub_of_is_ub(lower, s, b[j])])


@Theorem(
    ForAll([a, b], nested(I),
           ForAll(n, n >= 0, a[n] <= b[n]),
           Exists(x, iinter(I)[x]))
)
def nonempty_iinter_icc_of_nested(l):
    a, b = l.fixes()
    decreasing, ordered = l.intros()
    # Nesting separates all lower endpoints from all upper endpoints.
    cross_bounds = l.specialize(nested_icc_bounds, a, b, decreasing, ordered)
    between = l.specialize(exists_between_seq, a, b, cross_bounds)
    s = l.obtain(between)
    l.exists(s)
    l.auto(by=[iinter.defn, icc.defn])
