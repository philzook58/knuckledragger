"""
Axioms that could be in the Kernel, but aren't needed for everyday functioning of Knuckledragger
"""

import kdrag as kd
import kdrag.smt as smt
from typing import Sequence


def proj(p: kd.Proof, n: int) -> kd.Proof:
    """
    Project out of an And proof

    >>> x = smt.Int("x")
    >>> p = kd.prove(smt.And(x > x - 1, x > x - 2, x > x - 3))
    >>> proj(p, 0)
    |= x > x - 1
    >>> proj(p, 2)
    |= x > x - 3
    """
    assert isinstance(p, kd.Proof) and smt.is_and(p.thm)
    return kd.axiom(p.thm.arg(n), ["proj", p, n])


def eqrefl(x: smt.ExprRef) -> kd.Proof:
    """
    Prove reflexivity of equality

    >>> x = smt.Int("x")
    >>> eqrefl(x)
    |= x == x
    """
    assert isinstance(x, smt.ExprRef)
    return kd.axiom(smt.Eq(x, x), ["eqrefl", x])


def eqsym(eq: kd.Proof) -> kd.Proof:
    """
    Prove symmetry of equality

    >>> x, y = smt.Ints("x y")
    >>> eq = kd.axiom(x == y)
    >>> eqsym(eq)
    |= y == x
    """
    assert isinstance(eq, kd.Proof) and smt.is_eq(eq.thm)
    return kd.axiom(smt.Eq(eq.thm.arg(1), eq.thm.arg(0)), ["eqsym", eq])


def eqtrans(eq1: kd.Proof, eq2: kd.Proof) -> kd.Proof:
    """
    Prove transitivity of equality

    >>> x, y, z = smt.Ints("x y z")
    >>> eq1 = kd.axiom(x == y)
    >>> eq2 = kd.axiom(y == z)
    >>> eqtrans(eq1, eq2)
    |= x == z
    """
    assert isinstance(eq1, kd.Proof) and isinstance(eq2, kd.Proof)
    assert smt.is_eq(eq1.thm) and smt.is_eq(eq2.thm)
    assert eq1.thm.arg(1).eq(eq2.thm.arg(0))
    return kd.axiom(smt.Eq(eq1.thm.arg(0), eq2.thm.arg(1)), ["eqtrans", eq1, eq2])


def cong(f: smt.FuncDeclRef, *args: kd.Proof) -> kd.Proof:
    """
    Congruence of function symbols. If f is a function symbol, then f(x) == f(y) if x == y.

    >>> x = smt.Int("x")
    >>> y = smt.Real("y")
    >>> f = smt.Function("f", smt.IntSort(), smt.RealSort(), smt.IntSort())
    >>> cong(f, eqrefl(x), eqrefl(y))
    |= f(x, y) == f(x, y)
    """
    assert (
        isinstance(f, smt.FuncDeclRef)
        and f.arity() == len(args)
        and all(
            isinstance(a, kd.Proof)
            and smt.is_eq(a.thm)
            and a.thm.arg(0).sort() == f.domain(n)
            for n, a in enumerate(args)
        )
    )
    lhs = [a.thm.arg(0) for a in args]
    rhs = [a.thm.arg(1) for a in args]
    return kd.axiom(smt.Eq(f(*lhs), f(*rhs)), ["cong", f, *args])


def subst(eq: kd.Proof, t: smt.ExprRef) -> kd.Proof:
    """
    Substitute subterms using equality proof

    >>> x, y = smt.Ints("x y")
    >>> eq = kd.prove(x == ((x + 1) - 1))
    >>> subst(eq, x + 3)
    |= x + 3 == x + 1 - 1 + 3
    """
    assert isinstance(eq, kd.Proof) and smt.is_eq(eq.thm)
    return kd.axiom(
        t == smt.substitute(t, (eq.thm.arg(0), eq.thm.arg(1))), ["subst", eq, t]
    )


def ext(*sorts: smt.SortRef) -> kd.Proof:
    """
    >>> ext(smt.IntSort(), smt.IntSort())
    |= ForAll([f, g], (f == g) == (ForAll(x0, f[x0] == g[x0])))
    >>> ext(smt.IntSort(), smt.RealSort(), smt.IntSort())
    |= ForAll([f, g],
           (f == g) ==
           (ForAll([x0, x1],
                   Select(f, x0, x1) == Select(g, x0, x1))))
    """
    T = smt.ArraySort(*sorts)
    f, g = smt.Consts("f g", T)
    xs = [smt.Const(f"x{n}", sort) for n, sort in enumerate(sorts[:-1])]
    return kd.axiom(
        smt.ForAll([f, g], smt.Eq((f == g), smt.ForAll(xs, f[*xs] == g[*xs]))), ["ext"]
    )


def neg_ext(*sorts: smt.SortRef) -> kd.Proof:
    """

    >>> neg_ext(smt.IntSort(), smt.IntSort())
    |= ForAll([f, g], f != g == (Exists(x0, f[x0] != g[x0])))
    >>> neg_ext(smt.IntSort(), smt.RealSort(), smt.IntSort())
    |= ForAll([f, g],
           f != g ==
           (Exists([x0, x1],
                   Select(f, x0, x1) != Select(g, x0, x1))))
    """
    # TODO: Derive from ext?
    T = smt.ArraySort(*sorts)
    f, g = smt.Consts("f g", T)
    xs = [smt.Const(f"x{n}", sort) for n, sort in enumerate(sorts[:-1])]
    return kd.axiom(
        smt.ForAll([f, g], smt.Eq(f != g, smt.Exists(xs, f[*xs] != g[*xs]))), ["ext"]
    )


def unfold(e: smt.ExprRef, defn_eqs: Sequence[kd.Proof]):
    """
    Unfold a definitional equation. The order of variables is off from what kd.define returns.

    >>> x = smt.Int("x")
    >>> y = smt.Real("y")
    >>> f = smt.Function("test_f", smt.IntSort(), smt.RealSort(), smt.RealSort())
    >>> defn = kd.axiom(smt.ForAll([y,x], f(x,y) == (x + 2*y)))
    >>> unfold(f(7,8), [defn])
    |= test_f(7, 8) == ToReal(7) + 2*8
    """
    assert all(isinstance(pf, kd.Proof) for pf in defn_eqs)
    subst = []
    for pf in defn_eqs:
        thm = pf.thm
        if isinstance(thm, smt.QuantifierRef) and thm.is_forall():
            eq = thm.body()
            lhs, rhs = eq.arg(0), eq.arg(1)
            decl = lhs.decl()
            for n, v in enumerate(lhs.children()):
                assert smt.is_var(v) and smt.get_var_index(v) == n
            subst.append((decl, rhs))
        elif smt.is_eq(thm):
            lhs, rhs = thm.arg(0), thm.arg(1)
            assert smt.is_const(lhs)
            decl = lhs.decl()
            subst.append((decl, rhs))
        else:
            raise ValueError("Unfolding only works for definitional equalities", pf)
    return kd.axiom(e == smt.substitute_funs(e, *subst), by=["unfold", defn_eqs])


def beta_conv(lam: smt.QuantifierRef, *args) -> kd.Proof:
    """
    Beta conversion for lambda calculus.
    """
    assert len(args) == lam.num_vars()
    assert smt.is_quantifier(lam) and lam.is_lambda()
    return kd.axiom(smt.Eq(lam[args], smt.substitute_vars(lam.body(), *reversed(args))))


"""
TODO: For better Lemma
def modus_n(n: int, ab: Proof, bc: Proof):
    ""
    Plug together two theorems of the form
    Implies(And(ps), b), Implies(And(qs, b, rs),  c)
    -----------
    Implies(And(qs, ps, rs), c)

    Useful for backwards chaining.

    
    ""
    assert (
        is_proof(ab)
        and is_proof(bc)
        and smt.is_implies(ab.thm)
        and smt.is_implies(bc.thm)
    )
    aa = ab.thm.arg(0)
    assert smt.is_and(aa)
    aa = aa.children()
    b = ab.thm.arg(1)
    bb = bc.thm.arg(0)
    assert smt.is_and(bb)
    bb = bb.children()
    assert bb[n].eq(b)
    c = bc.thm.arg(1)
    return axiom(smt.Implies(smt.And(*bb[:n], *aa, *bb[n + 1 :]), c), [ab, bc])
"""
