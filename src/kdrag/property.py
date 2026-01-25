"""
Generic properties like associativity, commutativity, idempotence, etc.
"""

import kdrag.smt as smt


def Assoc(f, T=None) -> smt.BoolRef:
    """
    >>> Assoc(smt.Function("f", smt.IntSort(), smt.IntSort(), smt.IntSort()))
    ForAll([x, y, z], f(f(x, y), z) == f(x, f(y, z)))
    """
    if T is None:
        T = f.range()
    x, y, z = smt.Consts("x y z", T)
    return smt.ForAll([x, y, z], f(f(x, y), z) == f(x, f(y, z)))


def Comm(f, T=None) -> smt.BoolRef:
    """
    >>> Comm(smt.Function("f", smt.IntSort(), smt.IntSort(), smt.IntSort()))
    ForAll([x, y], f(x, y) == f(y, x))
    """
    if T is None:
        T = f.range()
    x, y = smt.Consts("x y", T)
    return smt.ForAll([x, y], f(x, y) == f(y, x))


def Idem(f, T=None) -> smt.BoolRef:
    """
    >>> Idem(smt.Function("f", smt.IntSort(), smt.IntSort(), smt.IntSort()))
    ForAll(x, f(x, x) == x)
    """
    if T is None:
        T = f.range()
    x = smt.Const("x", T)
    return smt.ForAll([x], f(x, x) == x)


def LeftIdentity(f, e: smt.ExprRef, T=None) -> smt.BoolRef:
    """
    >>> LeftIdentity(smt.Function("f", smt.IntSort(), smt.IntSort(), smt.IntSort()), smt.IntVal(0))
    ForAll(x, f(0, x) == x)
    """
    if T is None:
        T = f.range()
    x = smt.Const("x", T)
    return smt.ForAll([x], f(e, x) == x)


def RightIdentity(f, e: smt.ExprRef, T=None) -> smt.BoolRef:
    """
    >>> RightIdentity(smt.Function("f", smt.IntSort(), smt.IntSort(), smt.IntSort()), smt.IntVal(0))
    ForAll(x, f(x, 0) == x)
    """
    if T is None:
        T = f.range()
    x = smt.Const("x", T)
    return smt.ForAll([x], f(x, e) == x)


def SemiGroup(f) -> smt.BoolRef:
    return Assoc(f)


def AbelSemiGroup(f) -> smt.BoolRef:
    return smt.And(SemiGroup(f), Comm(f))


def Monoid(f, e: smt.ExprRef) -> smt.BoolRef:
    return smt.And(SemiGroup(f), LeftIdentity(f, e), RightIdentity(f, e))


def CommMonoid(f, e: smt.ExprRef) -> smt.BoolRef:
    return smt.And(AbelSemiGroup(f), LeftIdentity(f, e))


def SemiRing(add, mul, zero, one) -> smt.BoolRef:
    T = zero.sort()
    x, y, z = smt.Consts("x y z", T)
    return smt.And(
        CommMonoid(add, zero),
        Monoid(mul, one),
        smt.ForAll([x], mul(x, zero) == zero),
        smt.ForAll([x], mul(zero, x) == zero),
        smt.ForAll([x, y, z], mul(x, add(y, z)) == add(mul(x, y), mul(x, z))),
        smt.ForAll([x, y, z], mul(add(x, y), z) == add(mul(x, z), mul(y, z))),
    )


def StarSemiring(add, mul, zero, one, star):
    T = zero.sort()
    x, y = smt.Consts("x y", T)
    return smt.And(
        SemiRing(add, mul, zero, one),
        smt.ForAll([x], add(one, mul(x, star(x))) == star(x)),
        smt.ForAll([x], add(one, mul(star(x), x)) == star(x)),
    )


def CommSemiRing(add, mul, zero, one) -> smt.BoolRef:
    return smt.And(
        SemiRing(add, mul, zero, one),
        Comm(mul),
    )


def SemiLattice(join) -> smt.BoolRef:
    """
    >>> _ = SemiLattice(smt.Function("join", smt.IntSort(), smt.IntSort(), smt.IntSort()))
    """
    return smt.And(Assoc(join), Comm(join), Idem(join))


def Refl(rel) -> smt.BoolRef:
    """
    >>> Refl(smt.Function("rel", smt.IntSort(), smt.IntSort(), smt.BoolSort()))
    ForAll(x, rel(x, x))
    """
    T = rel.domain(0)
    x = smt.Const("x", T)
    return smt.ForAll([x], rel(x, x))


def Antisymm(rel) -> smt.BoolRef:
    """
    >>> Antisymm(smt.Function("rel", smt.IntSort(), smt.IntSort(), smt.BoolSort()))
    ForAll([x, y], Implies(And(rel(x, y), rel(y, x)), x == y))
    """
    T = rel.domain(0)
    x, y = smt.Consts("x y", T)
    return smt.ForAll([x, y], rel(x, y), rel(y, x), x == y)


def Trans(rel) -> smt.BoolRef:
    """
    >>> Trans(smt.Function("rel", smt.IntSort(), smt.IntSort(), smt.BoolSort()))
    ForAll([x, y, z], Implies(And(rel(x, y), rel(y, z)), rel(x, z)))
    """
    T = rel.domain(0)
    x, y, z = smt.Consts("x y z", T)
    return smt.ForAll([x, y, z], rel(x, y), rel(y, z), rel(x, z))


def PreOrder(rel) -> smt.BoolRef:
    return smt.And(Refl(rel), Trans(rel))


def PartialOrder(rel) -> smt.BoolRef:
    return smt.And(PreOrder(rel), Antisymm(rel))


"""
# A different attempt using Protocols

from typing import Protocol, runtime_checkable
import kdrag as kd
from . import smt

type SetRef = smt.FuncRef


# https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#Std.Associative
@runtime_checkable
class Assoc(Protocol):
    "forall x y z, f(f(x,y),z) = f(x,f(y,z))"

    # Should we make everything quantified only over a particular set?
    # S: SetRef
    f: smt.FuncDeclRef
    assoc: kd.Proof


@runtime_checkable
class Comm(Protocol):
    "forall x y, f(x,y) = f(y,x)"

    f: smt.FuncDeclRef
    comm: kd.Proof


@runtime_checkable
class Idem(Protocol):
    "forall x, f(x,x) = x"

    f: smt.FuncDeclRef
    idem: kd.Proof


@runtime_checkable
class LeftIdentity(Protocol):
    "forall x, f(e,x) = x"

    f: smt.FuncDeclRef
    e: smt.ExprRef
    left_id: kd.Proof


@runtime_checkable
class RightIdentity(Protocol):
    "forall x, f(x,e) = x"

    f: smt.FuncDeclRef
    e: smt.ExprRef
    right_id: kd.Proof


@runtime_checkable
class Identity(LeftIdentity, RightIdentity, Protocol): ...


@runtime_checkable
class Refl(Protocol):
    "forall x, rel(x, x)"

    rel: smt.FuncDeclRef
    refl: kd.Proof


@runtime_checkable
class Antisymm(Protocol):
    "forall x y, rel(x, y) and rel(y, x) implies x = y"

    rel: smt.FuncDeclRef
    antisymm: kd.Proof


@runtime_checkable
class Asymm(Protocol):
    "forall x y, rel(x, y) implies not rel(y, x)"

    rel: smt.FuncDeclRef
    asymm: kd.Proof


@runtime_checkable
class Total(Protocol):
    "forall x y, rel(x, y) or rel(y, x)"

    rel: smt.FuncDeclRef
    total: kd.Proof


@runtime_checkable
class Irrefl(Protocol):
    "forall x, not rel(x, x)"

    rel: smt.FuncDeclRef
    irrefl: kd.Proof
"""
