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


def forall_cong(vs: list[smt.ExprRef], pf: kd.Proof) -> kd.Proof:
    """
    Congruence for forall binders

    >>> x = smt.Bool("x")
    >>> forall_cong([x], kd.prove(x | x == x))
    |= (ForAll(x, Or(x, x))) == (ForAll(x, x))
    """
    assert isinstance(pf, kd.Proof) and smt.is_eq(pf.thm)
    return kd.axiom(
        smt.Eq(smt.ForAll(vs, pf.thm.arg(0)), smt.ForAll(vs, pf.thm.arg(1))),
        by=["forall_cong", pf],
    )


def exists_cong(vs: list[smt.ExprRef], pf: kd.Proof) -> kd.Proof:
    """
    Congruence for exists binders

    >>> x = smt.Bool("x")
    >>> exists_cong([x], kd.prove(x | x == x))
    |= (Exists(x, Or(x, x))) == (Exists(x, x))
    """

    assert isinstance(pf, kd.Proof) and smt.is_eq(pf.thm)
    return kd.axiom(
        smt.Eq(
            smt.Exists(vs, pf.thm.arg(0)),
            smt.Exists(vs, pf.thm.arg(1)),
        ),
        by=["exists_cong", pf],
    )


def lambda_cong(vs: list[smt.ExprRef], pf: kd.Proof) -> kd.Proof:
    """

    >>> x = smt.Int("x")
    >>> lambda_cong([x], kd.prove(x + 1 == 1 + x))
    |= (Lambda(x, x + 1)) == (Lambda(x, 1 + x))
    """
    assert isinstance(pf, kd.Proof) and smt.is_eq(pf.thm)
    return kd.axiom(
        smt.Eq(
            smt.Lambda(vs, pf.thm.arg(0)),
            smt.Lambda(vs, pf.thm.arg(1)),
        ),
        by=["lambda_cong", pf],
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


def substitute_fresh_vars(pf: kd.Proof, *subst) -> kd.Proof:
    """
    Substitute schematic variables in a theorem.
    This is is single step instead of generalizing to a Forall and then eliminating it.

    >>> x = kd.FreshVar("x", smt.IntSort())
    >>> y = kd.FreshVar("y", smt.IntSort())
    >>> substitute_fresh_vars(kd.kernel.prove(x == x), (x, smt.IntVal(42)), (y, smt.IntVal(43)))
    |= 42 == 42
    """
    assert all(kd.kernel.is_fresh_var(v) for v, t in subst) and isinstance(pf, kd.Proof)
    return kd.kernel.axiom(
        smt.substitute(pf.thm, *subst), by=["substitute_fresh_vars", pf, subst]
    )


def consider(x: smt.ExprRef) -> kd.Proof:
    """
    The purpose of this is to seed the solver with interesting terms.
    Axiom schema. We may give a fresh name to any constant. An "anonymous" form of define.
    Pointing out the interesting terms is sometimes the essence of a proof.
    """
    # should be the same as skolem(smt.Exists([t], t == x))
    return kd.axiom(smt.Eq(smt.FreshConst(x.sort(), prefix="consider"), x))


def rename_vars(
    t: smt.QuantifierRef,
    vs: list[smt.ExprRef],
) -> tuple[smt.QuantifierRef, kd.Proof]:
    """

    >>> x,y = smt.Ints("x y")
    >>> rename_vars(smt.ForAll([x, y], x + 1 > y), [y,x])
    (ForAll([y, x], y + 1 > x), |= (ForAll([x, y], x + 1 > y)) == (ForAll([y, x], y + 1 > x)))
    >>> rename_vars(smt.Exists([x], x + 1 > y), [y])
    Traceback (most recent call last):
        ...
    ValueError: ('Cannot rename vars to ones that already occur in term', [y], Exists(x, x + 1 > y))
    """
    assert isinstance(t, smt.QuantifierRef)
    t_body = t.body()
    body = smt.substitute_vars(t_body, *reversed(vs))
    if t.is_forall():
        t2 = smt.ForAll(vs, body)
    elif t.is_exists():
        t2 = smt.Exists(vs, body)
    elif t.is_lambda():
        t2 = smt.Lambda(vs, body)
    else:
        raise Exception("Unknown quantifier type", t)
    if not t2.body().eq(t_body):
        raise ValueError("Cannot rename vars to ones that already occur in term", vs, t)
    return t2, kd.axiom(t == t2, by=["rename", t, vs])


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
