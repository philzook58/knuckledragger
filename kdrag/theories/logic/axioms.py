"""
Axioms that could be in the Kernel, but aren't needed for everyday functioning of Knuckledragger
"""

import kdrag as kd
import kdrag.smt as smt


def proj(p: kd.Proof, n: int) -> kd.Proof:
    """
    Project out of an And proof

    >>> x = smt.Int("x")
    >>> p = kd.prove(smt.And(x > x - 1, x > x - 2, x > x - 3))
    >>> proj(p, 0)
    |- x > x - 1
    >>> proj(p, 2)
    |- x > x - 3
    """
    assert isinstance(p, kd.Proof) and smt.is_and(p.thm)
    return kd.axiom(p.thm.arg(n), ["proj", p, n])


def andI(a: kd.Proof, b: kd.Proof) -> kd.Proof:
    """
    Prove an and from two kd.Proofs of its conjuncts.

    >>> a, b = smt.Bools("a b")
    >>> pa = kd.axiom(a)
    >>> pb = kd.axiom(b)
    >>> andI(pa, pb)
    |- And(a, b)
    """
    assert isinstance(a, kd.Proof) and isinstance(b, kd.Proof)
    return kd.axiom(smt.And(a.thm, b.thm), ["andI", a, b])


def eqrefl(x: smt.ExprRef) -> kd.Proof:
    """
    Prove reflexivity of equality

    >>> x = smt.Int("x")
    >>> eqrefl(x)
    |- x == x
    """
    assert isinstance(x, smt.ExprRef)
    return kd.axiom(smt.Eq(x, x), ["eqrefl", x])


def eqsym(eq: kd.Proof) -> kd.Proof:
    """
    Prove symmetry of equality

    >>> x, y = smt.Ints("x y")
    >>> eq = kd.axiom(x == y)
    >>> eqsym(eq)
    |- y == x
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
    |- x == z
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
    |- f(x, y) == f(x, y)
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
    |- x + 3 == x + 1 - 1 + 3
    """
    assert isinstance(eq, kd.Proof) and smt.is_eq(eq.thm)
    return kd.axiom(
        t == smt.substitute(t, (eq.thm.arg(0), eq.thm.arg(1))), ["subst", eq, t]
    )


def beta_conv(lam: smt.QuantifierRef, *args) -> kd.Proof:
    """
    Beta conversion for lambda calculus.
    """
    assert len(args) == lam.num_vars()
    assert smt.is_quantifier(lam) and lam.is_lambda()
    return kd.axiom(smt.Eq(lam[args], smt.substitute_vars(lam.body(), *reversed(args))))
