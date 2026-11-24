"""Linear independence of finite lists of vectors (Axler 2A), and the effect of
deleting one vector and adding multiples of it to the others."""

from kdrag import Theorem, define
from kdrag.smt import (
    Const,
    Consts,
    Exists,
    ForAll,
    If,
    Int,
    Ints,
    Lambda,
    Not,
    Real,
    RealVal,
)
import kdrag.theories.int as int_
import kdrag.theories.real.rseq as rseq
from kdrag.theories.real.rseq import RSeq, krondelta, smul, zero
from kdrag.contrib.linalg.span import (
    Fam,
    add_smul,
    lincomb,
    lincomb_add,
    lincomb_congr,
    lincomb_krondelta,
    lincomb_smul,
    lincomb_succ,
    smul_smul,
    zero_smul,
)

c, d, v = Consts("c d v", RSeq)
F = Const("F", Fam)
x = Real("x")
n, m, j, k = Ints("n m j k")

# --- Independence (Axler 2.15) -------------------------------------------------

lin_indep = define(
    "linalg.lin_indep",
    [F, n],
    ForAll([c], lincomb(F, c, n) == zero, ForAll([j], 0 <= j, j < n, c[j] == 0)),
)


@Theorem(ForAll([F, n, j], 0 <= j, j < n, F[j] == zero, Not(lin_indep(F, n))))
def not_lin_indep_of_zero(l):
    F, n, j = l.fixes()
    l.intros()
    l.unfold(lin_indep)
    # krondelta(j) is a nonzero combination giving F[j] = 0
    l.have(lincomb(F, krondelta(j), n) == zero, by=[lincomb_krondelta(F, j, n)])
    l.auto(by=[krondelta.defn])


# --- Removing one vector from a family ------------------------------------------

remove_nth = define("linalg.remove_nth", [F, k], Lambda([j], If(j < k, F[j], F[j + 1])))
"""F with entry k deleted; later entries shift down by one."""
insert_nth_zero = define(
    "linalg.insert_nth_zero",
    [c, k],
    Lambda([j], If(j < k, c[j], If(j == k, RealVal(0), c[j - 1]))),
)
"""Coefficients c with a 0 inserted at position k; the inverse reindexing of remove_nth."""

p = Int("p")


@Theorem(
    ForAll(
        [F, d, k, p],
        k >= 0,
        p >= 0,
        lincomb(remove_nth(F, k), d, k + p)
        == lincomb(F, insert_nth_zero(d, k), k + p + 1),
    )
)
def lincomb_remove(l):
    """A combination of the shortened family is one of F with coefficient 0 at k."""
    F, d, k, p = l.fixes()
    l.intros()
    l.induct(p, using=int_.induct_nat)
    # p = 0: below k the families and coefficients agree; F[k] gets coefficient 0
    l.have(
        lincomb(remove_nth(F, k), d, k) == lincomb(F, insert_nth_zero(d, k), k),
        by=[
            lincomb_congr(remove_nth(F, k), F, d, insert_nth_zero(d, k), k),
            remove_nth.defn,
            insert_nth_zero.defn,
        ],
    )
    l.auto(
        by=[
            lincomb_succ(F, insert_nth_zero(d, k), k),
            insert_nth_zero.defn,
            zero_smul,
            rseq.add_zero,
        ]
    )
    # step: both sides gain d[k+p] • F[k+p+1]
    p = l.fix()
    l.intros()
    l.auto(
        by=[
            lincomb_succ(remove_nth(F, k), d, k + p),
            lincomb_succ(F, insert_nth_zero(d, k), k + p + 1),
            remove_nth.defn,
            insert_nth_zero.defn,
        ]
    )


# --- Shearing: add a multiple of one vector to the others ------------------------

s = Const("s", RSeq)
A, B = Consts("A B", Fam)


@Theorem(
    ForAll(
        [A, B, d, n],
        lincomb(Lambda([j], A[j] + B[j]), d, n) == lincomb(A, d, n) + lincomb(B, d, n),
    )
)
def lincomb_fam_add(l):
    """lincomb is additive in the family too."""
    A, B, d, n = l.fixes()
    l.induct(n)
    n = l.fix()
    l.intros()
    l.auto(by=[lincomb.defn, rseq.add_zero])
    l.auto(by=[lincomb.defn, rseq.add_zero])
    n = l.fix()
    l.intros()
    l.auto(
        by=[
            lincomb_succ(Lambda([j], A[j] + B[j]), d, n),
            lincomb_succ(A, d, n),
            lincomb_succ(B, d, n),
            rseq.add.defn,
            smul.defn,
        ]
    )


@Theorem(
    ForAll(
        [s, v, d, n],
        Exists([x], lincomb(Lambda([j], smul(s[j], v)), d, n) == smul(x, v)),
    )
)
def lincomb_line(l):
    """A combination of multiples of v is a multiple of v."""
    s, v, d, n = l.fixes()
    l.induct(n)
    n = l.fix()
    l.intros()
    l.exists(RealVal(0))
    l.auto(by=[lincomb.defn, zero_smul])
    l.exists(RealVal(0))
    l.auto(by=[lincomb.defn, zero_smul])
    # step: the new term d[n] • s[n] • v joins the multiple
    n = l.fix()
    l.intros()
    x0, _ = l.obtain(-1)
    l.exists(x0 + d[n] * s[n])
    l.auto(by=[lincomb_succ(Lambda([j], smul(s[j], v)), d, n), add_smul, smul_smul])


def shear(F, k, s):
    """F without F[k], with s[j] • F[k] added to the j-th remaining vector."""
    return Lambda([j], remove_nth(F, k)[j] + smul(s[j], F[k]))


@Theorem(
    ForAll(
        [F, k, m, s],
        0 <= k,
        k < m,
        lin_indep(F, m),
        lin_indep(shear(F, k, s), m - 1),
    )
)
def lin_indep_shear(l):
    F, k, m, s = l.fixes()
    l.intros()
    l.unfold(lin_indep)
    d0 = l.fix()
    l.intro()
    R = remove_nth(F, k)
    Ln = Lambda([j], smul(s[j], F[k]))
    # split the combination into the removed family plus a multiple of F[k]
    l.have(
        lincomb(shear(F, k, s), d0, m - 1)
        == lincomb(R, d0, m - 1) + lincomb(Ln, d0, m - 1),
        by=[lincomb_fam_add(R, Ln, d0, m - 1)],
    )
    x0, _ = l.obtain(
        l.have(
            Exists([x], lincomb(Ln, d0, m - 1) == smul(x, F[k])),
            by=[lincomb_line(s, F[k], d0, m - 1)],
        )
    )
    l.have(
        lincomb(R, d0, m - 1) == lincomb(F, insert_nth_zero(d0, k), m),
        by=[lincomb_remove(F, d0, k, m - 1 - k)],
    )
    # so a combination of F with coefficients e vanishes
    e = insert_nth_zero(d0, k) + smul(x0, krondelta(k))
    l.have(
        lincomb(F, e, m) == lincomb(F, insert_nth_zero(d0, k), m) + smul(x0, F[k]),
        by=[
            lincomb_add(F, insert_nth_zero(d0, k), smul(x0, krondelta(k)), m),
            lincomb_smul(F, krondelta(k), x0, m),
            lincomb_krondelta(F, k, m),
        ],
    )
    l.have(lincomb(F, e, m) == zero, by=[])
    # independence of F kills e, and e is d0 with an entry inserted at k
    l.have(ForAll([j], 0 <= j, j < m, e[j] == 0), by=[lin_indep.defn(F, m)])
    i = l.fix()
    l.intros()
    l.cases(i < k)
    # below k, d0[i] sits at e[i]
    l.have(e[i] == 0, by=[])
    l.auto(by=[insert_nth_zero.defn, rseq.add.defn, smul.defn, krondelta.defn])
    # from k on, d0[i] sits at e[i + 1]
    l.have(e[i + 1] == 0, by=[])
    l.auto(by=[insert_nth_zero.defn, rseq.add.defn, smul.defn, krondelta.defn])
