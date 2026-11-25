"""An independent list is no longer than a spanning list (Axler 2.22).

The proof inducts on the spanning length, eliminating the last spanning vector
from the coefficient matrix as in Gaussian elimination.
"""

from kdrag import Theorem
from kdrag.smt import And, Consts, Exists, ForAll, Ints, Lambda, Real
import kdrag.theories.int as int_
import kdrag.theories.real.rseq as rseq
from kdrag.theories.real.rseq import RSeq, smul
from kdrag.contrib.linalg.span import (
    Fam,
    exists_coeffs_of_mem_span,
    lincomb,
    lincomb_add,
    lincomb_smul,
    lincomb_succ,
    span,
    zero_smul,
)
from kdrag.contrib.linalg.indep import (
    lin_indep,
    lin_indep_shear,
    not_lin_indep_of_zero,
    remove_nth,
    shear,
)

c, d = Consts("c d", RSeq)
F, G, C = Consts("F G C", Fam)
x = Real("x")
n, m, j, k = Ints("n m j k")


@Theorem(
    ForAll(
        [G, c, d, x, n],
        n >= 0,
        c[n] + x * d[n] == 0,
        lincomb(G, c, n + 1) + smul(x, lincomb(G, d, n + 1))
        == lincomb(G, c + smul(x, d), n),
    )
)
def row_shear(l):
    """Eliminating the last coefficient: the new row needs only G[0..n)."""
    G, c, d, x, n = l.fixes()
    l.intros()
    l.have(
        lincomb(G, c + smul(x, d), n + 1)
        == lincomb(G, c, n + 1) + smul(x, lincomb(G, d, n + 1)),
        by=[lincomb_add(G, c, smul(x, d), n + 1), lincomb_smul(G, d, x, n + 1)],
    )
    l.have((c + smul(x, d))[n] == 0, by=[rseq.add.defn, smul.defn])
    l.auto(by=[lincomb_succ(G, c + smul(x, d), n), zero_smul, rseq.add_zero])


t = Real("t")


def elim(C, k, n, t):
    """Multipliers that clear column n of the rows other than k, given t = 1 / C[k][n]."""
    return Lambda([j], -(remove_nth(C, k)[j][n] * t))


@Theorem(
    ForAll(
        [G, F, C, n, m, k, t],
        n >= 0,
        0 <= k,
        k < m,
        t * C[k][n] == 1,
        ForAll([j], 0 <= j, j < m, F[j] == lincomb(G, C[j], n + 1)),
        ForAll(
            [j],
            0 <= j,
            j < m - 1,
            shear(F, k, elim(C, k, n, t))[j]
            == lincomb(G, shear(C, k, elim(C, k, n, t))[j], n),
        ),
    )
)
def shear_rows(l):
    """Row reduction on the coefficient matrix C mirrors the shear on F."""
    G, F, C, n, m, k, t = l.fixes()
    l.intros()
    i = l.fix()
    l.intros()
    sc = elim(C, k, n, t)
    l.have(
        remove_nth(F, k)[i] == lincomb(G, remove_nth(C, k)[i], n + 1),
        by=[remove_nth.defn],
    )
    l.have(F[k] == lincomb(G, C[k], n + 1), by=[])
    l.have(remove_nth(C, k)[i][n] + sc[i] * C[k][n] == 0, by=[])
    l.auto(by=[row_shear(G, remove_nth(C, k)[i], C[k], sc[i], n)])


@Theorem(ForAll([x], x != 0, Exists([t], t * x == 1)))
def exists_inv(l):
    x = l.fix()
    l.intro()
    l.exists(1 / x)
    l.auto()


def bounded_by(n):
    """Every independent family spanned (via a coefficient matrix) by n vectors has length <= n."""
    return ForAll(
        [G, F, m, C],
        m >= 0,
        lin_indep(F, m),
        ForAll([j], 0 <= j, j < m, F[j] == lincomb(G, C[j], n)),
        m <= n,
    )


@Theorem(
    ForAll(
        [n, G, F, m, C, k],
        n >= 0,
        bounded_by(n),
        0 <= k,
        k < m,
        C[k][n] != 0,
        lin_indep(F, m),
        ForAll([j], 0 <= j, j < m, F[j] == lincomb(G, C[j], n + 1)),
        m <= n + 1,
    )
)
def bounded_by_succ_elim(l):
    """Row k uses G[n]: eliminate G[n] from the other rows with row k, leaving
    m - 1 independent vectors spanned by G[0..n)."""
    n1, G1, F1, m1, C1, k1 = l.fixes()
    _, ih, _, _, _, _, _ = l.intros()
    t1, _ = l.obtain(
        l.have(Exists([t], t * C1[k1][n1] == 1), by=[exists_inv(C1[k1][n1])])
    )
    sc = elim(C1, k1, n1, t1)
    l.have(lin_indep(shear(F1, k1, sc), m1 - 1), by=[lin_indep_shear(F1, k1, m1, sc)])
    l.have(
        ForAll(
            [j],
            0 <= j,
            j < m1 - 1,
            shear(F1, k1, sc)[j] == lincomb(G1, shear(C1, k1, sc)[j], n1),
        ),
        by=[shear_rows(G1, F1, C1, n1, m1, k1, t1)],
    )
    l.specialize(ih, G1, shear(F1, k1, sc), m1 - 1, shear(C1, k1, sc))
    l.auto()


@Theorem(
    ForAll(
        [n, G, F, m, C],
        n >= 0,
        bounded_by(n),
        m >= 0,
        lin_indep(F, m),
        ForAll([j], 0 <= j, j < m, F[j] == lincomb(G, C[j], n + 1)),
        m <= n + 1,
    )
)
def bounded_by_succ(l):
    """The induction step of 2.22."""
    n1, G1, F1, m1, C1 = l.fixes()
    _, ih, _, _, _ = l.intros()
    uses_last = Exists([k], And(0 <= k, k < m1, C1[k][n1] != 0))
    l.cases(uses_last)
    # some row uses G[n]
    k1, _ = l.obtain(l.have(uses_last, by=[]))
    l.auto(by=[bounded_by_succ_elim(n1, G1, F1, m1, C1, k1)])
    # no row uses G[n]: G[0..n) already spans F, so the IH applies directly
    l.have(
        ForAll([j], 0 <= j, j < m1, F1[j] == lincomb(G1, C1[j], n1)),
        by=[lincomb_succ, zero_smul, rseq.add_zero],
    )
    l.specialize(ih, G1, F1, m1, C1)
    l.auto()


@Theorem(ForAll([n], n >= 0, bounded_by(n)))
def lin_indep_le_of_coeffs(l):
    """2.22 with the spanning coefficients given as a matrix C (rows C[j])."""
    n = l.fix()
    l.intro()
    l.induct(n, using=int_.induct_nat)
    # n = 0: every F[j] is the empty combination, i.e. zero, so the family is empty
    G1, F1, m1, C1 = l.fixes()
    l.intros()
    l.auto(by=[lincomb.defn(G1, C1[0], 0), not_lin_indep_of_zero(F1, m1, 0)])
    # step
    n1 = l.fix()
    l.intros()
    G1, F1, m1, C1 = l.fixes()
    l.intros()
    l.auto(by=[bounded_by_succ(n1, G1, F1, m1, C1)])


@Theorem(
    ForAll(
        [F, G, m, n],
        n >= 0,
        lin_indep(F, m),
        ForAll([j], 0 <= j, j < m, span(G, n)[F[j]]),
        m <= n,
    )
)
def lin_indep_le_span(l):
    """Axler 2.22: an independent list is no longer than a spanning list."""
    F1, G1, m1, n1 = l.fixes()
    l.intros()
    C1, _ = l.obtain(
        l.have(
            Exists([C], ForAll([j], 0 <= j, j < m1, F1[j] == lincomb(G1, C[j], n1))),
            by=[exists_coeffs_of_mem_span(F1, G1, n1, m1)],
        )
    )
    l.cases(m1 >= 0)
    # m >= 0: the matrix form, at the chosen C
    l.have(bounded_by(n1), by=[lin_indep_le_of_coeffs(n1)])
    l.specialize(-1, G1, F1, m1, C1)
    l.auto()
    # m < 0 <= n
    l.auto()
