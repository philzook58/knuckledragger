"""
Generic properties like associativity, commutativity, idempotence, etc.
"""

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
    """
    forall x, rel(x, x)
    """

    rel: smt.FuncDeclRef
    refl: kd.Proof


@runtime_checkable
class Antisymm(Protocol):
    """
    forall x y, rel(x, y) and rel(y, x) implies x = y
    """

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
