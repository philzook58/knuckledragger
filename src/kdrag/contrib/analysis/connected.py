"""Connected subsets of the real line and the intermediate value theorem."""

from kdrag import Theorem, define
from kdrag.notation import Image
from kdrag.smt import And, Const, Consts, EmptySet, Eq, Exists, ForAll, Lambda, Or
import kdrag.theories.real as real
from kdrag.theories.real import rset
from kdrag.theories.real.rseq import a, ge_of_has_lim, has_lim, le_of_has_lim, n

from .cont import cont_on, cont_on_mono, cont_within_at, has_lim_comp_of_cont_within_at
from .topology import (
    exists_seq_of_mem_closure,
    mem_closure_of_has_lim,
    mem_closure_of_is_lub,
)

A, B, E, G = Consts("A B E G", real.RSet)
f = Const("f", real.RFun)
x, y = real.x, real.y
lo, hi, level = real.a, real.b, real.u


def _partition(E, A, B):
    return And(
        Eq(E, A | B), Eq(A & B, EmptySet(real.R)), Exists(x, A[x]), Exists(x, B[x])
    )


def _touches(A, B):
    return Exists(x, B[x], real.closure(A)[x])


is_connected = define(
    "analysis.is_connected",
    E,
    ForAll([A, B], _partition(E, A, B), Or(_touches(A, B), _touches(B, A))),
)


def _seq_crosses(A, B):
    return Exists([a, x], And(ForAll(n, n >= 0, A[a[n]]), has_lim(a, x), B[x]))


@Theorem(ForAll([A, B], Eq(_touches(A, B), _seq_crosses(A, B))))
def _touches_iff_seq_crosses(l):
    A, B = l.fixes()
    l.split()
    point, witness = l.obtain(l.intro())
    _, near = l.andE(witness)
    seq, witness = l.obtain(l.specialize(exists_seq_of_mem_closure, A, point, near))
    l.andE(witness)
    l.exists(seq, point)
    l.auto()
    (seq, point), witness = l.obtain(l.intro())
    l.andE(witness)
    l.exists(point)
    l.auto(by=[mem_closure_of_has_lim(A, seq, point)])


def _sequence_property(E):
    return ForAll(
        [A, B], _partition(E, A, B), Or(_seq_crosses(A, B), _seq_crosses(B, A))
    )


@Theorem(ForAll(E, Eq(is_connected(E), _sequence_property(E))))
def is_connected_iff_seq(l):
    """Abbott 3.4.6."""
    l.fix()
    l.unfold(is_connected)
    l.split()
    for _ in range(2):
        condition = l.intro()
        A, B = l.fixes()
        l.intro()
        l.specialize(condition, A, B)
        l.auto(by=[_touches_iff_seq_crosses(A, B), _touches_iff_seq_crosses(B, A)])


preimage = define("analysis.preimage", [f, A], Lambda(x, A[f[x]]))


@Theorem(ForAll([f, E, x], E[x], Image(f, E)[f[x]]))
def mem_image_of_mem(l):
    f, E, x = l.fixes()
    l.intro()
    l.beta()
    l.exists(x)
    l.auto()


@Theorem(
    ForAll(
        [f, E, A], A <= Image(f, E), Exists(y, A[y]), Exists(x, (E & preimage(f, A))[x])
    )
)
def _exists_mem_preimage(l):
    f, E, A = l.fixes()
    _, nonempty = l.intros()
    y, _ = l.obtain(nonempty)
    member = l.have(Exists(x, E[x], y == f[x]), by=[])
    point, _ = l.obtain(member)
    l.exists(point)
    l.auto(by=[preimage.defn(f, A)])


@Theorem(
    ForAll(
        [f, E, A, B],
        _partition(Image(f, E), A, B),
        _partition(E, E & preimage(f, A), E & preimage(f, B)),
    )
)
def _partition_preimage(l):
    f, E, A, B = l.fixes()
    l.andE(l.intro())
    l.split()
    l.ext()
    x = l.fix()
    l.auto(by=[mem_image_of_mem(f, E, x), preimage.defn(f, A), preimage.defn(f, B)])
    l.ext()
    x = l.fix()
    l.auto(by=[preimage.defn(f, A), preimage.defn(f, B)])
    l.auto(by=[_exists_mem_preimage(f, E, A)])
    l.auto(by=[_exists_mem_preimage(f, E, B)])


@Theorem(
    ForAll(
        [f, E, A, B],
        cont_on(f, E),
        _seq_crosses(E & preimage(f, A), E & preimage(f, B)),
        _seq_crosses(A, B),
    )
)
def _seq_crosses_image(l):
    f, E, A, B = l.fixes()
    _, crossing = l.intros()
    (seq, point), witness = l.obtain(crossing)
    in_pullback, _, _ = l.andE(witness)
    mapped = Lambda(n, f[seq[n]])
    l.have(ForAll(n, n >= 0, And(E[seq[n]], A[mapped[n]])))
    j = l.fix()
    l.intro()
    l.specialize(in_pullback, j)
    l.auto(by=[preimage.defn(f, A)])
    l.clear(in_pullback)
    l.have(cont_within_at(f, E, point), by=[cont_on.defn(f, E)])
    l.exists(mapped, f[point])
    l.auto(by=[has_lim_comp_of_cont_within_at(seq, f, E, point), preimage.defn(f, B)])


@Theorem(
    ForAll([f, G, E], cont_on(f, G), E <= G, is_connected(E), is_connected(Image(f, E)))
)
def is_connected_image(l):
    """Abbott 4.5.2."""
    f, G, E = l.fixes()
    l.intros()
    l.have(cont_on(f, E), by=[cont_on_mono(f, G, E)])
    image = Image(f, E)
    l.rw(is_connected_iff_seq(image))
    A, B = l.fixes()
    l.intro()
    C, D = E & preimage(f, A), E & preimage(f, B)
    # Pull the partition back, then map the crossing sequence forward.
    partition = l.have(_partition(E, C, D), by=[_partition_preimage(f, E, A, B)])
    connected = l.have(_sequence_property(E), by=[is_connected_iff_seq(E)])
    l.specialize(connected, C, D, partition)
    l.auto(by=[_seq_crosses_image(f, E, A, B), _seq_crosses_image(f, E, B, A)])


@Theorem(ForAll([E, lo, x, hi], is_connected(E), E[lo], E[hi], lo < x, x < hi, E[x]))
def mem_of_is_connected_of_between(l):
    E, lo, point, hi = l.fixes()
    l.intros()
    l.contra()
    # If the point is missing, the two sides of the gap partition E.
    left = Lambda(x, And(E[x], x < point))
    right = Lambda(x, And(E[x], point < x))
    l.have(_partition(E, left, right))
    l.split()
    l.ext()
    l.fix()
    l.auto()
    l.ext()
    l.fix()
    l.auto()
    l.exists(lo)
    l.auto()
    l.exists(hi)
    l.auto()
    connected = l.have(_sequence_property(E), by=[is_connected_iff_seq(E)])
    l.specialize(connected, left, right)
    l.cases(_seq_crosses(left, right), _seq_crosses(right, left))
    (seq, limit), witness = l.obtain(_seq_crosses(left, right))
    l.andE(witness)
    l.have(ForAll(n, n >= 0, seq[n] <= point), by=[])
    l.auto(by=[le_of_has_lim(seq, limit, point)])
    (seq, limit), witness = l.obtain(_seq_crosses(right, left))
    l.andE(witness)
    l.have(ForAll(n, n >= 0, point <= seq[n]), by=[])
    l.auto(by=[ge_of_has_lim(seq, limit, point)])


def _contains_between(E):
    return ForAll([lo, x, hi], E[lo], E[hi], lo <= x, x <= hi, E[x])


@Theorem(
    ForAll(
        [E, A, B, lo, hi],
        _contains_between(E),
        _partition(E, A, B),
        A[lo],
        B[hi],
        lo < hi,
        Or(_touches(A, B), _touches(B, A)),
    )
)
def _touches_of_ordered_partition(l):
    E, A, B, lo, hi = l.fixes()
    interval, partition, *_ = l.intros()
    l.andE(partition)
    lower = A & real.icc(lo, hi)
    # Take the supremum of the first side between the chosen endpoints.
    l.have(Exists(x, lower[x]))
    l.exists(lo)
    l.auto(by=[real.icc.defn(lo, hi)])
    l.have(rset.bdd_above(lower))
    l.unfold(rset.bdd_above)
    l.exists(hi)
    l.unfold(rset.is_ub)
    l.fix()
    l.intro()
    l.auto(by=[real.icc.defn(lo, hi)])
    supremum = l.have(
        Exists(x, rset.is_lub(lower, x)), by=[rset.exists_is_lub_of_bdd_above(lower)]
    )
    s, _ = l.obtain(supremum)
    l.have(rset.is_ub(lower, s), by=[rset.is_ub_of_is_lub(lower, s)])
    l.have(
        And(lo <= s, s <= hi),
        by=[
            real.icc.defn(lo, hi),
            rset.is_ub.defn(lower, hi),
            rset.le_of_mem_of_is_ub(lower, lo, s),
            rset.le_of_is_lub_of_is_ub(lower, s, hi),
        ],
    )
    l.specialize(interval, lo, s, hi, keep=True)
    l.cases(A[s], B[s])
    # If the supremum is on the first side, nearby points to its right are on the second.
    l.right()
    l.exists(s)
    l.split()
    l.auto()
    l.unfold(real.closure)
    l.beta()
    radius = l.fix()
    l.intro()
    point = s + real.min(radius, hi - s) / 2
    l.have(
        And(s < point, point <= hi, point < s + radius),
        by=[real.min.defn(radius, hi - s)],
    )
    l.specialize(interval, lo, point, hi)
    l.exists(point)
    l.auto(
        by=[
            real.icc.defn(lo, hi),
            real.ball.defn(s, radius),
            rset.le_of_mem_of_is_ub(lower, point, s),
        ]
    )
    # If it is on the second side, the points approaching the supremum lie on the first.
    l.left()
    l.exists(s)
    l.split()
    l.auto()
    l.have(real.closure(lower)[s], by=[mem_closure_of_is_lub(lower, s)])
    l.unfold(real.closure)
    l.beta()
    radius = l.fix()
    positive = l.intro()
    approximants = l.have(
        real.closure.defn(lower).thm.arg(1)(s), by=[real.closure.defn(lower)]
    )
    point, _ = l.obtain(l.specialize(approximants, radius, positive))
    l.exists(point)
    l.auto()


@Theorem(ForAll(E, _contains_between(E), is_connected(E)))
def is_connected_of_contains_between(l):
    E = l.fix()
    l.intro()
    l.unfold(is_connected)
    A, B = l.fixes()
    partition = l.intro()
    _, _, in_A, in_B = l.andE(partition)
    a, _ = l.obtain(in_A)
    b, _ = l.obtain(in_B)
    l.auto(
        by=[
            _touches_of_ordered_partition(E, A, B, a, b),
            _touches_of_ordered_partition(E, B, A, b, a),
        ]
    )


@Theorem(ForAll([lo, hi], is_connected(real.icc(lo, hi))))
def is_connected_icc(l):
    lo, hi = l.fixes()
    interval = real.icc(lo, hi)
    l.have(_contains_between(interval))
    l.fixes()
    l.intros()
    l.auto(by=[real.icc.defn(lo, hi)])
    l.auto(by=[is_connected_of_contains_between(interval)])


@Theorem(
    ForAll(
        [f, lo, hi, level],
        lo < hi,
        cont_on(f, real.icc(lo, hi)),
        Or(And(f[lo] < level, level < f[hi]), And(f[hi] < level, level < f[lo])),
        Exists(x, lo < x, x < hi, f[x] == level),
    )
)
def intermediate_value(l):
    """Abbott 4.5.1, via preservation of connectedness."""
    f, lo, hi, level = l.fixes()
    l.intros()
    interval = real.icc(lo, hi)
    image = Image(f, interval)
    l.have(
        is_connected(image),
        by=[is_connected_icc(lo, hi), is_connected_image(f, interval, interval)],
    )
    l.have(
        And(image[f[lo]], image[f[hi]]),
        by=[
            real.icc.defn(lo, hi),
            mem_image_of_mem(f, interval, lo),
            mem_image_of_mem(f, interval, hi),
        ],
    )
    member = l.have(
        Exists(x, interval[x], level == f[x]),
        by=[
            mem_of_is_connected_of_between(image, f[lo], level, f[hi]),
            mem_of_is_connected_of_between(image, f[hi], level, f[lo]),
        ],
    )
    point, _ = l.obtain(member)
    l.exists(point)
    l.auto(by=[real.icc.defn(lo, hi)])
