import kdrag as kd
import kdrag.smt as smt

# import kdrag.property as prop
from typing import Protocol, runtime_checkable


# https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Defs.html#Semigroup
# https://isabelle.in.tum.de/library/HOL/HOL/Groups.html
@runtime_checkable
class SemiGroup(Protocol):
    """
    A Semigroup is a set with an associative binary operation.
    mul_assoc : forall x y z, mul (mul x y)
    """

    mul: smt.FuncDeclRef
    mul_assoc: kd.Proof


def check_semigroup(S: SemiGroup):
    T = S.mul.domain(0)
    x, y, z = smt.Consts("x y z", T)
    assert kd.utils.alpha_eq(
        S.mul_assoc.thm,
        smt.ForAll([x, y, z], S.mul(S.mul(x, y), z) == S.mul(x, S.mul(y, z))),
    )


@runtime_checkable
class AddSemigroup(Protocol):
    add: smt.FuncDeclRef
    add_assoc: kd.Proof


@runtime_checkable
class CommSemigroup(SemiGroup, Protocol):
    mul: smt.FuncDeclRef
    mul_comm: kd.Proof
    mul_assoc: kd.Proof


@runtime_checkable
class CommAddSemigroup(AddSemigroup, Protocol):
    add: smt.FuncDeclRef
    add_comm: kd.Proof
    add_assoc: kd.Proof


@runtime_checkable
class Monoid(SemiGroup, Protocol):
    """
    A Monoid is a Semigroup with an identity element.
    one_mul : forall x, one * x = x
    mul_one : forall x, x * one = x
    """

    one: smt.ExprRef
    one_mul: kd.Proof
    mul_one: kd.Proof


@runtime_checkable
class Group(Monoid, Protocol):
    """
    A Group is a Monoid with an inverse element.
    mul_left_inv : forall x, inv x * x = one
    mul_right_inv : forall x, x * inv x = one
    """

    inv: smt.FuncDeclRef
    mul_left_inv: kd.Proof
    mul_right_inv: kd.Proof
