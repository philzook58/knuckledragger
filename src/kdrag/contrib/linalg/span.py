"""Linear combinations and spans of finite lists of vectors (Axler 2A).

Vectors are real sequences `RSeq = Int -> Real`. A list of vectors is a family
`F : Int -> RSeq` together with a length n; only `F[0..n)` matters. The span is
the smallest subspace containing the list (Halmos §11), and `mem_span_iff`
shows it is the set of linear combinations.
"""

from kdrag import Theorem, define, prove
from kdrag.smt import (
    And,
    ArraySort,
    BoolSort,
    Const,
    Consts,
    Exists,
    ForAll,
    Function,
    If,
    Implies,
    IntSort,
    Ints,
    Lambda,
    Reals,
    Store,
)
import kdrag.theories.real.rseq as rseq
from kdrag.theories.real.rseq import RSeq, krondelta, smul, zero

Fam = ArraySort(IntSort(), RSeq)
VSet = ArraySort(RSeq, BoolSort())

u, v, w, c, d = Consts("u v w c d", RSeq)
F, G = Consts("F G", Fam)
C = Const("C", Fam)
U = Const("U", VSet)
x, y = Reals("x y")
n, m, j = Ints("n m j")

# --- RSeq vector-space prelude ------------------------------------------------

add_smul = prove(
    ForAll([x, y, u], smul(x + y, u) == smul(x, u) + smul(y, u)),
    by=[smul.defn, rseq.add.defn],
)
smul_smul = prove(
    ForAll([x, y, u], smul(x, smul(y, u)) == smul(x * y, u)), by=[smul.defn]
)
zero_smul = prove(ForAll([u], smul(0, u) == zero), by=[smul.defn, zero.defn])
smul_zero = prove(ForAll([x], smul(x, zero) == zero), by=[smul.defn, zero.defn])
one_smul = prove(ForAll([u], smul(1, u) == u), by=[smul.defn])
zero_add = prove(ForAll([u], zero + u == u), by=[rseq.add.defn, zero.defn])

is_subspace = define(
    "linalg.is_subspace",
    [U],
    And(
        U[zero],
        ForAll([u, v], U[u], U[v], U[u + v]),
        ForAll([x, u], U[u], U[smul(x, u)]),
    ),
)

# --- Linear combinations (Axler 2.2) -----------------------------------------

lincomb = Function("linalg.lincomb", Fam, RSeq, IntSort(), RSeq)
lincomb = define(
    "linalg.lincomb",
    [F, c, n],
    If(n <= 0, zero, lincomb(F, c, n - 1) + smul(c[n - 1], F[n - 1])),
)

lincomb_succ = prove(
    ForAll(
        [F, c, n], n >= 0, lincomb(F, c, n + 1) == lincomb(F, c, n) + smul(c[n], F[n])
    ),
    by=[lincomb.defn],
)


@Theorem(ForAll([F, n], lincomb(F, zero, n) == zero))
def lincomb_coeff_zero(l):
    F, n = l.fixes()
    l.induct(n)
    # n <= 0: the empty combination
    n = l.fix()
    l.intros()
    l.auto(by=[lincomb.defn])
    l.auto(by=[lincomb.defn])
    # step: the new term is 0 • F[n]
    n = l.fix()
    l.intros()
    l.auto(by=[lincomb_succ(F, zero, n), zero.defn, zero_smul, rseq.add_zero])


@Theorem(
    ForAll([F, c, d, n], lincomb(F, c + d, n) == lincomb(F, c, n) + lincomb(F, d, n))
)
def lincomb_add(l):
    F, c, d, n = l.fixes()
    l.induct(n)
    n = l.fix()
    l.intros()
    l.auto(by=[lincomb.defn, rseq.add_zero])
    l.auto(by=[lincomb.defn, rseq.add_zero])
    # step: regroup the two new terms pointwise
    n = l.fix()
    l.intros()
    l.auto(
        by=[
            lincomb_succ(F, c + d, n),
            lincomb_succ(F, c, n),
            lincomb_succ(F, d, n),
            rseq.add.defn,
            smul.defn,
        ]
    )


@Theorem(ForAll([F, c, x, n], lincomb(F, smul(x, c), n) == smul(x, lincomb(F, c, n))))
def lincomb_smul(l):
    F, c, x, n = l.fixes()
    l.induct(n)
    n = l.fix()
    l.intros()
    l.auto(by=[lincomb.defn, smul_zero])
    l.auto(by=[lincomb.defn, smul_zero])
    n = l.fix()
    l.intros()
    l.auto(
        by=[
            lincomb_succ(F, smul(x, c), n),
            lincomb_succ(F, c, n),
            rseq.add.defn,
            smul.defn,
        ]
    )


@Theorem(
    ForAll(
        [F, G, c, d, n],
        ForAll([j], 0 <= j, j < n, And(F[j] == G[j], c[j] == d[j])),
        lincomb(F, c, n) == lincomb(G, d, n),
    )
)
def lincomb_congr(l):
    """Only `F[0..n)` and `c[0..n)` matter."""
    F, G, c, d, n = l.fixes()
    l.induct(n)
    n = l.fix()
    l.intros()
    l.auto(by=[lincomb.defn])
    l.auto(by=[lincomb.defn])
    # step: agreement on [0, n+1) restricts to [0, n) and gives the new term
    n = l.fix()
    l.intros()
    l.auto(by=[lincomb_succ(F, c, n), lincomb_succ(G, d, n)])


@Theorem(ForAll([F, j, n], 0 <= j, j < n, lincomb(F, krondelta(j), n) == F[j]))
def lincomb_krondelta(l):
    F, j, n = l.fixes()
    l.induct(n)
    n = l.fix()
    l.intros()
    l.auto()
    l.auto()
    n = l.fix()
    l.intros()
    # j == n: the earlier coefficients vanish, so only 1 • F[n] remains
    l.have(
        Implies(j == n, lincomb(F, krondelta(j), n) == lincomb(F, zero, n)),
        by=[lincomb_congr(F, F, krondelta(j), zero, n), krondelta.defn, zero.defn],
    )
    l.auto(
        by=[
            lincomb_succ(F, krondelta(j), n),
            lincomb_coeff_zero(F, n),
            krondelta.defn,
            zero_add,
            zero_smul,
            one_smul,
            rseq.add_zero,
        ]
    )


@Theorem(
    ForAll(
        [U, F, c, n],
        is_subspace(U),
        ForAll([j], 0 <= j, j < n, U[F[j]]),
        U[lincomb(F, c, n)],
    )
)
def lincomb_mem(l):
    U, F, c, n = l.fixes()
    l.induct(n)
    n = l.fix()
    l.intros()
    l.auto(by=[lincomb.defn, is_subspace.defn])
    l.auto(by=[lincomb.defn, is_subspace.defn])
    # step: U is closed under adding c[n] • F[n]
    n = l.fix()
    l.intros()
    l.auto(by=[lincomb_succ(F, c, n), is_subspace.defn(U)])


# --- Span as the smallest subspace (Halmos §11), with coefficients as a theorem --

span = define(
    "linalg.span",
    [F, n],
    Lambda([v], ForAll([U], is_subspace(U), ForAll([j], 0 <= j, j < n, U[F[j]]), U[v])),
)


@Theorem(ForAll([F, n], is_subspace(span(F, n))))
def span_is_subspace(l):
    F, n = l.fixes()
    l.unfold(is_subspace, at=None)
    l.unfold(span)
    l.beta()
    # every closure property is inherited from each U in the intersection
    l.auto(by=[is_subspace.defn])


@Theorem(ForAll([F, n, j], 0 <= j, j < n, span(F, n)[F[j]]))
def subset_span(l):
    F, n, j = l.fixes()
    l.intros()
    l.unfold(span)
    l.beta()
    l.auto()


@Theorem(
    ForAll(
        [U, F, n],
        is_subspace(U),
        ForAll([j], 0 <= j, j < n, U[F[j]]),
        ForAll([v], span(F, n)[v], U[v]),
    )
)
def span_le(l):
    """The span is the smallest subspace containing the list (Axler 2.6)."""
    U, F, n = l.fixes()
    l.intros()
    l.fix()
    l.intro()
    l.unfold(span, at=-1)
    l.beta(at=-1)
    l.auto()


combos = define(
    "linalg.combos", [F, n], Lambda([v], Exists([c], v == lincomb(F, c, n)))
)
"""All linear combinations of F[0..n)."""


@Theorem(ForAll([F, n], is_subspace(combos(F, n))))
def combos_is_subspace(l):
    F, n = l.fixes()
    l.unfold(is_subspace)
    l.unfold(combos)
    l.beta()
    l.split()
    # zero: all coefficients zero
    l.exists(zero)
    l.auto(by=[lincomb_coeff_zero(F, n)])
    # sums: add the coefficients
    u, v = l.fixes()
    l.intros()
    c0, _ = l.obtain(-2)
    d0, _ = l.obtain(-1)
    l.exists(c0 + d0)
    l.auto(by=[lincomb_add(F, c0, d0, n)])
    # scalings: scale the coefficients
    x, u = l.fixes()
    l.intro()
    c0, _ = l.obtain(-1)
    l.exists(smul(x, c0))
    l.auto(by=[lincomb_smul(F, c0, x, n)])


@Theorem(ForAll([F, n, j], 0 <= j, j < n, combos(F, n)[F[j]]))
def mem_combos(l):
    F, n, j = l.fixes()
    l.intros()
    l.unfold(combos)
    l.beta()
    l.exists(krondelta(j))
    l.auto(by=[lincomb_krondelta(F, j, n)])


@Theorem(ForAll([F, v, n], span(F, n)[v] == Exists([c], v == lincomb(F, c, n))))
def mem_span_iff(l):
    """The span is the set of linear combinations (Axler 2.7 / Halmos §11)."""
    F, v, n = l.fixes()
    l.split()
    # <- : a combination lies in every subspace containing F[0..n), span included
    l.intro()
    c0, _ = l.obtain(-1)
    l.auto(by=[lincomb_mem(span(F, n), F, c0, n), span_is_subspace(F, n), subset_span])
    # -> : the combinations form a subspace containing F[0..n)
    l.intro()
    l.have(ForAll([j], 0 <= j, j < n, combos(F, n)[F[j]]), by=[mem_combos])
    l.have(combos(F, n)[v], by=[span_le(combos(F, n), F, n), combos_is_subspace(F, n)])
    l.unfold(combos, at=-1)
    l.beta(at=-1)
    l.auto()


@Theorem(
    ForAll(
        [F, G, n, m],
        ForAll([j], 0 <= j, j < m, span(G, n)[F[j]]),
        Exists([C], ForAll([j], 0 <= j, j < m, F[j] == lincomb(G, C[j], n))),
    )
)
def exists_coeffs_of_mem_span(l):
    """Finite choice: pick one coefficient sequence per vector, as rows of C."""
    F, G, n, m = l.fixes()
    l.induct(m)
    # m <= 0: nothing to choose
    m = l.fix()
    l.intros()
    l.exists(G)
    l.auto()
    l.intro()
    l.exists(G)
    l.auto()
    # step: rows for j < m from the IH, row m from F[m] being in the span
    m = l.fix()
    l.intros()
    l.have(ForAll([j], 0 <= j, j < m, span(G, n)[F[j]]), by=[])
    C0, _ = l.obtain(
        l.have(
            Exists([C], ForAll([j], 0 <= j, j < m, F[j] == lincomb(G, C[j], n))), by=[]
        )
    )
    c0, _ = l.obtain(
        l.have(Exists([c], F[m] == lincomb(G, c, n)), by=[mem_span_iff(G, F[m], n)])
    )
    l.exists(Store(C0, m, c0))
    l.auto()
