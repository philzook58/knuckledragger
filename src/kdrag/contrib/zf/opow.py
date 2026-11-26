"""
Ordinal exponentiation (Halmos §21).

α^β is defined by transfinite recursion on β: α^0 = 1, α^(β+1) = α^β·α, and
at a limit λ, α^λ is the supremum (union) of the α^β with β < λ. The recursion
step sees δ and the earlier values t; δ is a successor exactly when
δ = (⋃δ)⁺, and then ⋃δ is its predecessor.
"""

from kdrag import Theorem, define, prove
from kdrag.smt import And, ArraySort, Consts, Exists, ForAll, If, Lambda
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import ZFSet, bigunion, elem, le, succ, zero
from kdrag.contrib.zf.fun import app
from kdrag.contrib.zf.nat import (
    elem_succ,
    elem_succ_self,
    omega,
    omega_succ,
    omega_zero,
    one,
    succ_ne_zero,
)
from kdrag.contrib.zf.omul import omul, one_omul
from kdrag.contrib.zf.ordinal import (
    elem_repl,
    is_ordinal,
    is_ordinal_of_elem,
    is_ordinal_succ,
    nat_is_ordinal,
    omega_is_ordinal,
    repl,
)
from kdrag.contrib.zf.ordset import ordinal_le_of_elem, ordinal_not_elem_self, ordinal_well_order
from kdrag.contrib.zf.poset import nat_le_rel, seg, well_order_induction
from kdrag.contrib.zf.orec import app_orec, orec, oval

A, B, L, a, b, d, t, x, y = Consts("A B L a b d t x y", ZFSet)


@Theorem(ForAll(B, is_ordinal(B), bigunion(succ(B)) == B))
def bigunion_succ(l):
    """The predecessor of β⁺ is ⋃β⁺ = β, as β is transitive."""
    B = l.fix()
    l.intro()
    l.rw(zf.ext_ax)
    l.fix()
    l.rw(zf.bigunion_ax)
    l.split()
    l.intro()
    C0, _ = l.obtain(-1)
    l.auto(by=[elem_succ(C0, B), ordinal_le_of_elem(B, C0), le.defn(C0, B)])
    l.intro()
    l.exists(B)
    l.auto(by=[elem_succ(B, B)])


# The values of t below d, as a set.
vals = define("vals", [t, d], repl(Lambda(y, app(t, y)), d))


@Theorem(ForAll([t, d, x], elem(x, vals(t, d)) == Exists(y, And(elem(y, d), app(t, y) == x))))
def elem_vals(l):
    t, d, x0 = l.fixes()
    l.unfold(vals)
    l.auto(by=[elem_repl(Lambda(y, app(t, y)), d, x0)])


opow_step = define(
    "opow_step",
    [A, d, t],
    If(
        d == zero,
        one,
        If(d == succ(bigunion(d)), omul(app(t, bigunion(d)), A), bigunion(vals(t, d))),
    ),
)
G = Consts("G", ArraySort(ZFSet, ZFSet, ZFSet))[0]
opow_rec = define("opow_rec", [A], Lambda([d, t], opow_step(A, d, t)))


@Theorem(ForAll([A, d, t], opow_rec(A)[d, t] == opow_step(A, d, t)))
def opow_rec_apply(l):
    l.fixes()
    l.unfold(opow_rec)
    l.simp()
    l.auto()


opow = define("opow", [A, B], oval(opow_rec(A), B))


@Theorem(ForAll(A, opow(A, zero) == one))
def opow_zero(l):
    """Halmos: α^0 = 1."""
    l.fix()
    l.unfold(opow)
    l.unfold(oval)
    l.rw(opow_rec_apply)
    l.unfold(opow_step)
    l.simp()
    l.auto()


@Theorem(ForAll([A, B], is_ordinal(B), opow(A, succ(B)) == omul(opow(A, B), A)))
def opow_succ(l):
    """Halmos: α^(β+1) = α^β·α."""
    A, B = l.fixes()
    l.intro()
    Gr = opow_rec(A)
    S = succ(B)
    t0 = orec(Gr, S)
    l.have(
        opow(A, S) == opow_step(A, S, t0),
        by=[opow.defn(A, S), oval.defn(Gr, S), opow_rec_apply(A, S, t0)],
    )
    # β⁺ is a successor with predecessor β, and the sequence's value at β is α^β.
    l.have(
        app(t0, B) == opow(A, B),
        by=[app_orec(Gr, S, B), is_ordinal_succ(B), elem_succ_self(B), opow.defn],
    )
    l.auto(by=[opow_step.defn(A, S, t0), succ_ne_zero(B), bigunion_succ(B)])


@Theorem(
    ForAll(
        [A, L, x],
        is_ordinal(L),
        L != zero,
        L != succ(bigunion(L)),
        elem(x, opow(A, L)) == Exists(y, And(elem(y, L), elem(x, opow(A, y)))),
    )
)
def elem_opow_limit(l):
    """Halmos: at a limit λ, α^λ is the union of the α^β with β < λ."""
    A, L, x0 = l.fixes()
    l.intros()
    Gr = opow_rec(A)
    t0 = orec(Gr, L)
    l.have(
        opow(A, L) == bigunion(vals(t0, L)),
        by=[opow.defn(A, L), oval.defn(Gr, L), opow_rec_apply(A, L, t0), opow_step.defn(A, L, t0)],
    )
    l.have(ForAll(y, elem(y, L), app(t0, y) == opow(A, y)), by=[app_orec, opow.defn])
    l.rw(-2)
    l.rw(zf.bigunion_ax)
    # x is in some α^β with β < λ, which is the value of the sequence at β.
    l.split()
    l.intro()
    y1, _ = l.obtain(-1)
    l.exists(opow(A, y1))
    l.auto(by=[elem_vals(t0, L, opow(A, y1))])
    l.intro()
    C1, _ = l.obtain(-1)
    l.have(Exists(y, And(elem(y, L), app(t0, y) == C1)), by=[elem_vals(t0, L, C1)])
    y2, _ = l.obtain(-1)
    l.exists(y2)
    l.auto()


@Theorem(ForAll(A, is_ordinal(A), opow(A, one) == A))
def opow_one(l):
    """α^1 = α^0·α = 1·α = α."""
    A = l.fix()
    l.intro()
    l.auto(by=[opow_succ(A, zero), opow_zero(A), one_omul(A), nat_is_ordinal(zero), omega_zero])


@Theorem(And(omega != zero, omega != succ(bigunion(omega))))
def omega_limit(l):
    """ω is a limit ordinal: ω = u⁺ would put u⁺ = ω in ω."""
    l.split()
    l.auto(by=[omega_zero, zero.defn, zf.elem_emp])
    l.intro()
    u = bigunion(omega)
    l.have(elem(u, omega), by=[elem_succ_self(u)])
    l.have(elem(omega, omega), by=[omega_succ(u)])
    l.auto(by=[ordinal_not_elem_self(omega, omega), omega_is_ordinal])


elem_opow_omega = prove(
    ForAll([A, x], elem(x, opow(A, omega)) == Exists(y, And(elem(y, omega), elem(x, opow(A, y))))),
    by=[elem_opow_limit, omega_limit, omega_is_ordinal],
)


@Theorem(ForAll(B, is_ordinal(B), opow(one, B) == one))
def one_opow(l):
    """1^β = 1, by transfinite induction through the zero, successor, and limit
    cases."""
    B = l.fix()
    l.intro()
    S = succ(B)
    l.have(is_ordinal(S), by=[is_ordinal_succ(B)])
    P = Lambda(x, opow(one, x) == one)
    l.have(ForAll(a, elem(a, S), ForAll(b, elem(b, seg(nat_le_rel, S, a)), P[b]), P[a]))
    a0 = l.fix()
    l.intros()
    l.have(seg(nat_le_rel, S, a0) == a0, by=[is_ordinal.defn(S)])
    l.have(is_ordinal(a0), by=[is_ordinal_of_elem(S, a0)])
    l.have(ForAll(b, elem(b, a0), opow(one, b) == one))
    l.auto()
    l.simp()
    u = bigunion(a0)
    l.cases(a0 == zero, a0 == succ(u), And(a0 != zero, a0 != succ(u)))
    l.auto(by=[opow_zero(one)])
    # 1^(γ+1) = 1^γ·1 = 1·1 = 1, with γ = ⋃δ < δ.
    l.have(elem(u, a0), by=[elem_succ_self(u)])
    l.have(is_ordinal(u), by=[is_ordinal_of_elem(a0, u)])
    l.auto(by=[opow_succ(one, u), one_omul(one), nat_is_ordinal(one), omega_succ(zero), omega_zero])
    # At a limit, 1^λ is the union of copies of 1 below λ, and λ ≠ 0.
    l.rw(zf.ext_ax)
    x0 = l.fix()
    l.have(
        elem(x0, opow(one, a0)) == Exists(y, And(elem(y, a0), elem(x0, opow(one, y)))),
        by=[elem_opow_limit(one, a0, x0)],
    )
    l.have(Exists(y, elem(y, a0)), by=[zf.not_emp_exists_elem(a0), zero.defn])
    y0, _ = l.obtain(-1)
    l.auto()
    l.have(
        ForAll(a, elem(a, S), P[a]),
        by=[well_order_induction(nat_le_rel, S, P), ordinal_well_order(S)],
    )
    l.have(P[B], by=[elem_succ_self(B)])
    l.simp(at=-1)
    l.auto()
