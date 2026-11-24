"""Sequential compactness of real sets and the nested compact set property."""

from kdrag import Theorem, define
from kdrag.smt import (
    And,
    Const,
    Eq,
    Exists,
    ForAll,
    If,
    IntVal,
    Lambda,
    Reals,
    substitute,
    ToInt,
    ToReal,
)
from kdrag.notation import Image
import kdrag.theories.real as real
from kdrag.theories.real import rset
from kdrag.theories.real.rseq import (
    F,
    a,
    dommap,
    eventually,
    f,
    has_lim,
    lim_unique,
    n,
    x,
    y,
)
from kdrag.theories.real.rset import An, M, nested, nested_subset, z

from ._choice import exists_seq_of_forall_exists
from .cauchy import is_bounded_nonneg_of_is_cauchy, is_cauchy_of_has_lim
from .cont import cont_on, cont_within_at, has_lim_comp_of_cont_within_at
from .rseq import has_lim_congr_nonneg
from .subsequence import (
    bolzano_weierstrass,
    has_lim_subseq,
    is_bounded_nonneg,
    is_subseq_index,
    le_subseq_index,
)
from .topology import (
    is_closed_icc,
    is_closed_of_seq_limits,
    mem_of_has_lim_of_eventually_mem,
    mem_of_is_glb_of_is_closed,
    mem_of_is_lub_of_is_closed,
)

A = real.A

is_compact = define(
    "analysis.is_compact",
    A,
    ForAll(
        a,
        ForAll(n, n >= 0, A[a[n]]),
        Exists([F, x], And(is_subseq_index(F), has_lim(dommap(F, a), x), A[x])),
    ),
)
is_bounded = define(
    "analysis.is_bounded",
    A,
    Exists(M, M > 0, ForAll(x, A[x], real.abs(x) <= M)),
)


@Theorem(
    ForAll(
        [A, a],
        is_compact(A),
        ForAll(n, n >= 0, A[a[n]]),
        Exists([F, x], And(is_subseq_index(F), has_lim(dommap(F, a), x), A[x])),
    )
)
def exists_subseq_of_is_compact(l):
    A, a = l.fixes()
    l.unfold(is_compact)
    compact, in_set = l.intros()
    l.specialize(compact, a, in_set)
    l.auto()


@Theorem(ForAll(A, is_compact(A), real.is_closed(A)))
def is_closed_of_is_compact(l):
    A = l.fix()
    compact = l.intro()
    l.have(ForAll([a, x], ForAll(n, n >= 0, A[a[n]]), has_lim(a, x), A[x]))
    seq, point = l.fixes()
    in_set, _ = l.intros()
    (idx, limit), witness = l.obtain(
        l.specialize(exists_subseq_of_is_compact, A, seq, compact, in_set)
    )
    l.andE(witness)
    subseq = dommap(idx, seq)
    l.have(has_lim(subseq, point), by=[has_lim_subseq(seq, idx, point)])
    l.auto(by=[lim_unique(subseq, limit, point)])
    l.auto(by=[is_closed_of_seq_limits(A)])


@Theorem(ForAll(A, is_compact(A), is_bounded(A)))
def is_bounded_of_is_compact(l):
    A = l.fix()
    compact = l.intro()
    l.unfold(is_bounded)
    l.contra()
    # If the set is unbounded, choose a term with magnitude above n + 1.
    far = Lambda([n, x], And(A[x], real.abs(x) > ToReal(n) + 1))
    l.have(ForAll(n, n >= 0, Exists(x, far[n, x])))
    j = l.fix()
    l.intro()
    l.beta()
    l.contra()
    l.have(Exists(M, M > 0, ForAll(x, A[x], real.abs(x) <= M)))
    l.exists(ToReal(j) + 1)
    l.split()
    l.auto()
    l.fix()
    l.intro()
    l.auto()
    l.auto()
    chosen = l.have(
        Exists(a, ForAll(n, n >= 0, far[n, a[n]])),
        by=[exists_seq_of_forall_exists(far)],
    )
    seq, large = l.obtain(chosen)
    in_set = l.have(ForAll(n, n >= 0, A[seq[n]]), by=[])
    (idx, limit), witness = l.obtain(
        l.specialize(exists_subseq_of_is_compact, A, seq, compact, in_set)
    )
    l.andE(witness)
    subseq = dommap(idx, seq)
    l.have(
        is_bounded_nonneg(subseq),
        by=[
            is_cauchy_of_has_lim(subseq, limit),
            is_bounded_nonneg_of_is_cauchy(subseq),
        ],
    )
    bounded = l.have(
        Exists(M, ForAll(n, n >= 0, real.abs(subseq[n]) <= M)),
        by=[is_bounded_nonneg.defn(subseq)],
    )
    B, bound = l.obtain(bounded)
    j = If(B < 0, IntVal(0), ToInt(B) + 1)
    l.have(idx[j] >= j, by=[le_subseq_index(idx, j)])
    l.specialize(large, idx[j])
    l.specialize(bound, j)
    l.auto(by=[dommap.defn(idx, seq)])


@Theorem(ForAll(A, real.is_closed(A), is_bounded(A), is_compact(A)))
def is_compact_of_is_closed_of_is_bounded(l):
    A = l.fix()
    l.unfold(is_bounded, is_compact)
    _, bounded = l.intros()
    B, bound = l.obtain(bounded)
    _, bounds = l.andE(bound)
    seq = l.fix()
    in_set = l.intro()
    bounded_seq = l.have(is_bounded_nonneg(seq))
    l.unfold(is_bounded_nonneg)
    l.exists(B)
    j = l.fix()
    l.intro()
    l.specialize(in_set, j)
    l.specialize(bounds, seq[j])
    l.auto()

    (idx, limit), witness = l.obtain(
        l.specialize(bolzano_weierstrass, seq, bounded_seq)
    )
    l.andE(witness)
    subseq = dommap(idx, seq)
    l.have(eventually(Lambda(n, A[subseq[n]])))
    l.unfold(eventually)
    l.exists(IntVal(0))
    j = l.fix()
    l.intro()
    l.have(idx[j] >= j, by=[le_subseq_index(idx, j)])
    l.specialize(in_set, idx[j])
    l.auto(by=[dommap.defn(idx, seq)])
    l.exists(idx, limit)
    l.auto(by=[mem_of_has_lim_of_eventually_mem(A, subseq, limit)])


@Theorem(ForAll(A, Eq(is_compact(A), And(real.is_closed(A), is_bounded(A)))))
def is_compact_iff_is_closed_and_bounded(l):
    """Abbott 3.3.4."""
    A = l.fix()
    l.auto(
        by=[
            is_closed_of_is_compact(A),
            is_bounded_of_is_compact(A),
            is_compact_of_is_closed_of_is_bounded(A),
        ]
    )


@Theorem(ForAll([x, y], is_compact(real.icc(x, y))))
def is_compact_icc(l):
    """Closed intervals are compact (Abbott 3.3.2)."""
    lo, hi = l.fixes()
    interval = real.icc(lo, hi)
    l.have(is_bounded(interval))
    l.unfold(is_bounded)
    l.exists(real.abs(lo) + real.abs(hi) + 1)
    l.split()
    l.auto(by=[real.abs_pos(lo), real.abs_pos(hi)])
    point = l.fix()
    l.intro()
    l.auto(
        by=[
            real.abs.defn(point),
            real.abs.defn(lo),
            real.abs.defn(hi),
            real.icc.defn(lo, hi),
        ]
    )
    l.auto(by=[is_closed_icc(lo, hi), is_compact_of_is_closed_of_is_bounded(interval)])


@Theorem(
    ForAll(
        An,
        nested(An),
        ForAll(n, n >= 0, is_compact(An[n])),
        ForAll(n, n >= 0, Exists(x, An[n][x])),
        Exists(x, real.iinter(An)[x]),
    )
)
def nonempty_iinter_of_nested_compact(l):
    """Nested nonempty compact sets have a common point (Abbott 3.3.5)."""
    sets = l.fix()
    _, compacts, _ = l.intros()
    point_in_set = Lambda([n, x], sets[n][x])
    chosen = l.have(
        Exists(a, ForAll(n, n >= 0, point_in_set[n, a[n]])),
        by=[exists_seq_of_forall_exists(point_in_set)],
    )
    seq, belongs = l.obtain(chosen)
    in_first = l.have(ForAll(n, n >= 0, sets[0][seq[n]]))
    j = l.fix()
    l.intro()
    l.specialize(belongs, j)
    l.auto(by=[nested_subset(sets, 0, j)])

    first = l.have(is_compact(sets[0]), by=[])
    (idx, limit), witness = l.obtain(
        l.specialize(exists_subseq_of_is_compact, sets[0], seq, first, in_first)
    )
    l.andE(witness)
    l.exists(limit)
    l.unfold(real.iinter)
    l.beta()
    m = l.fix()
    l.intro()
    l.specialize(compacts, m)
    subseq = dommap(idx, seq)
    # The subsequence eventually lies in each fixed set.
    l.have(eventually(Lambda(n, sets[m][subseq[n]])))
    l.unfold(eventually)
    l.exists(m)
    j = l.fix()
    l.intro()
    l.have(idx[j] >= j, by=[le_subseq_index(idx, j)])
    l.specialize(belongs, idx[j])
    l.auto(by=[nested_subset(sets, m, idx[j]), dommap.defn(idx, seq)])
    l.auto(
        by=[
            is_closed_of_is_compact(sets[m]),
            mem_of_has_lim_of_eventually_mem(sets[m], subseq, limit),
        ]
    )


K = Const("K", real.RSet)
_image = Image(f, K)


@Theorem(ForAll([f, A, K], cont_on(f, A), K <= A, is_compact(K), is_compact(_image)))
def is_compact_image(l):
    """The image of a compact subset of the domain is compact (Abbott 4.4.1)."""
    f, A, K = l.fixes()
    _, _, compact = l.intros()
    l.unfold(is_compact)
    seq = l.fix()
    in_image = l.intro()

    # Lift each image term to a point of the original compact set.
    preimage = Lambda([n, x], And(K[x], seq[n] == f[x]))
    l.have(ForAll(n, n >= 0, Exists(x, preimage[n, x])))
    j = l.fix()
    l.intro()
    l.specialize(in_image, j)
    l.beta()
    l.auto()
    lifted = l.have(
        Exists(a, ForAll(n, n >= 0, preimage[n, a[n]])),
        by=[exists_seq_of_forall_exists(preimage)],
    )
    source, points = l.obtain(lifted)
    in_K = l.have(ForAll(n, n >= 0, K[source[n]]), by=[])
    (idx, point), witness = l.obtain(
        l.specialize(exists_subseq_of_is_compact, K, source, compact, in_K)
    )
    l.andE(witness)

    # The same index map gives a convergent subsequence in the image.
    subseq = dommap(idx, source)
    l.have(ForAll(n, n >= 0, A[subseq[n]]))
    j = l.fix()
    l.intro()
    l.have(idx[j] >= j, by=[le_subseq_index(idx, j)])
    l.specialize(in_K, idx[j])
    l.auto(by=[dommap.defn(idx, source)])
    l.have(cont_within_at(f, A, point), by=[cont_on.defn(f, A)])
    mapped = Lambda(n, f[subseq[n]])
    l.have(
        has_lim(mapped, f[point]),
        by=[has_lim_comp_of_cont_within_at(subseq, f, A, point)],
    )
    target = dommap(idx, seq)
    l.have(ForAll(n, n >= 0, mapped[n] == target[n]))
    j = l.fix()
    l.intro()
    l.have(idx[j] >= j, by=[le_subseq_index(idx, j)])
    l.specialize(points, idx[j])
    l.auto(by=[dommap.defn(idx, source), dommap.defn(idx, seq)])
    l.have(
        has_lim(target, f[point]), by=[has_lim_congr_nonneg(mapped, target, f[point])]
    )

    l.exists(idx, f[point])
    l.beta()
    l.split()
    l.auto()
    l.auto()
    l.exists(point)
    l.auto()


@Theorem(
    ForAll(
        A,
        is_compact(A),
        Exists(x, A[x]),
        Exists([x, y], A[x], A[y], rset.is_glb(A, x), rset.is_lub(A, y)),
    )
)
def exists_extrema_of_is_compact(l):
    """A nonempty compact set contains its infimum and supremum."""
    A = l.fix()
    l.intros()
    l.have(is_bounded(A), by=[is_bounded_of_is_compact(A)])
    bound = l.have(is_bounded.defn(A).thm.arg(1), by=[is_bounded.defn(A)])
    radius, witness = l.obtain(bound)
    _, bounds = l.andE(witness)
    l.have(rset.bdd_below(A))
    l.unfold(rset.bdd_below)
    l.exists(-radius)
    l.unfold(rset.is_lb)
    point = l.fix()
    l.intro()
    l.specialize(bounds, point)
    l.auto(by=[real.abs_le(point, radius)])
    l.have(rset.bdd_above(A))
    l.unfold(rset.bdd_above)
    l.exists(radius)
    l.unfold(rset.is_ub)
    point = l.fix()
    l.intro()
    l.specialize(bounds, point)
    l.auto(by=[real.abs_le(point, radius)])

    infimum = l.have(
        Exists(x, rset.is_glb(A, x)), by=[rset.exists_is_glb_of_bdd_below(A)]
    )
    supremum = l.have(
        Exists(y, rset.is_lub(A, y)), by=[rset.exists_is_lub_of_bdd_above(A)]
    )
    lo, _ = l.obtain(infimum)
    hi, _ = l.obtain(supremum)
    l.exists(lo, hi)
    l.auto(
        by=[
            is_closed_of_is_compact(A),
            mem_of_is_glb_of_is_closed(A, lo),
            mem_of_is_lub_of_is_closed(A, hi),
        ]
    )


lo, hi = Reals("lo hi")


@Theorem(
    ForAll(
        [f, K, lo, hi],
        _image[lo],
        _image[hi],
        rset.is_lb(_image, lo),
        rset.is_ub(_image, hi),
        Exists([x, y], K[x], K[y], ForAll(z, K[z], And(f[x] <= f[z], f[z] <= f[y]))),
    )
)
def _exists_extrema_on_of_extrema_image(l):
    f, K, lo, hi = l.fixes()
    l.intros()
    image = Image(f, K)
    # The extreme image values have preimages in K.
    lower = l.have(Exists(x, K[x], lo == f[x]), by=[])
    upper = l.have(Exists(y, K[y], hi == f[y]), by=[])
    xmin, _ = l.obtain(lower)
    xmax, _ = l.obtain(upper)
    l.exists(xmin, xmax)
    l.split()
    l.auto()
    l.auto()
    point = l.fix()
    l.intro()
    l.have(image[f[point]])
    l.beta()
    l.exists(point)
    l.auto()
    l.auto(
        by=[rset.is_lb.defn(image, lo), rset.le_of_mem_of_is_ub(image, f[point], hi)]
    )


@Theorem(ForAll([f, K], Exists(x, K[x]), Exists(x, _image[x])))
def _image_nonempty(l):
    function, domain = l.fixes()
    point, _ = l.obtain(l.intro())
    l.exists(function[point])
    l.beta()
    l.exists(point)
    l.auto()


@Theorem(
    ForAll(
        [f, K],
        Exists(
            [x, y], _image[x], _image[y], rset.is_glb(_image, x), rset.is_lub(_image, y)
        ),
        Exists([x, y], K[x], K[y], ForAll(z, K[z], And(f[x] <= f[z], f[z] <= f[y]))),
    )
)
def _exists_extrema_on_of_image_contains_extrema(l):
    function, domain = l.fixes()
    image = substitute(_image, (f, function), (K, domain))
    (lo, hi), bounds = l.obtain(l.intro())
    lo_mem, hi_mem, _, _ = l.andE(bounds)
    lower = l.have(rset.is_lb(image, lo), by=[rset.is_glb.defn(image, lo)])
    upper = l.have(rset.is_ub(image, hi), by=[rset.is_ub_of_is_lub(image, hi)])
    l.specialize(
        _exists_extrema_on_of_extrema_image,
        function,
        domain,
        lo,
        hi,
        lo_mem,
        hi_mem,
        lower,
        upper,
    )
    l.auto()


@Theorem(
    ForAll(
        [f, K],
        cont_on(f, K),
        is_compact(K),
        Exists(x, K[x]),
        Exists([x, y], K[x], K[y], ForAll(z, K[z], And(f[x] <= f[z], f[z] <= f[y]))),
    )
)
def extreme_value_theorem(l):
    """A continuous function on a nonempty compact set attains both extrema."""
    function, domain = l.fixes()
    image = substitute(_image, (f, function), (K, domain))
    l.auto(
        by=[
            is_compact_image(function, domain, domain),
            _image_nonempty(function, domain),
            exists_extrema_of_is_compact(image),
            _exists_extrema_on_of_image_contains_extrema(function, domain),
        ]
    )
