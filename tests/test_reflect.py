import pytest

import kdrag as kd
import kdrag.contracts
import kdrag.smt as smt
from kdrag.reflect import reflect

@reflect
def vapp1000(n : int, m : int, 
         xs : "smt.ExprRef # kd.Vec(n, kd.Z)", 
         ys : "smt.ExprRef # kd.Vec(m, kd.Z)",
         )->  "smt.ExprRef # kd.Vec(n + m, kd.Z)":
    return xs + ys

foo = kd.define("foo342442", [], smt.IntVal(42))
@reflect
def bar3424(x : "{x for x in int if x > 0}") -> "{y for y in int if y == x + 42}":
    () = foo.defn
    return x + 42

@reflect
def add_nat(x: kd.Nat, y: kd.Nat) -> kd.Nat:
    match x:
        case S(n):
            return kd.Nat.S(add_nat(n, y))
        case Z():
            return y


@reflect
def guarded_match(x: int, y: int) -> int:
    match x:
        case 0:
            return y
        case _ if y > 0:
            return y + 1
        case _:
            return y - 1


z = smt.Int("z")


@reflect
def inc_pos(
    n: int, m: "smt.Lambda([z], smt.And(z > 0, z > n))"
) -> "smt.Lambda([z], z > n)":
    return n + m


@reflect
def repeated_case(x: int) -> int:
    match x:
        case 4:
            return x
        case 4:
            assert False
            return x
        case _:
            return x


def test_reflect_match_on_nat():
    x, y = smt.Consts("x y", kd.Nat)
    expected = smt.ForAll(
        [x, y],
        add_nat(x, y) == smt.If(kd.Nat.is_S(x), kd.Nat.S(add_nat(kd.Nat.pred(x), y)), y),
    )
    assert add_nat.defn.thm.body().eq(expected.body())


def test_reflect_match_guard_and_fallback():
    x, y = smt.Ints("x y")
    expected = smt.ForAll(
        [x, y],
        guarded_match(x, y) == smt.If(x == 0, y, smt.If(y > 0, y + 1, y - 1)),
    )
    assert guarded_match.defn.thm.body().eq(expected.body())



def test_reflect_unreachable_match_case_does_not_trip_assert():
    x = smt.Int("x")
    expected = smt.ForAll(
        [x], repeated_case(x) == smt.If(x == 4, x, smt.If(x == 4, x, x))
    )
    assert repeated_case.defn.thm.body().eq(expected.body())


class C:
    K = 4


@reflect
def match_global_value(x: int) -> int:
    match x:
        case C.K:
            return 1
        case _:
            return 0


def test_reflect_match_value_pattern_from_global():
    x = smt.Int("x")
    expected = smt.ForAll([x], match_global_value(x) == smt.If(x == 4, 1, 0))
    assert match_global_value.defn.thm.body().eq(expected.body())


def test_requires_ensures():
    @reflect
    def silly_inc(x: int) -> int:
        requires(x > 0)
        requires(x < 100)
        ensures(silly_inc(x) == x + 1)
        ensures(silly_inc(x) <= 101)
        return x + 1
    x = smt.Int("x")
    print(silly_inc.contract.thm.sexpr())
    print(smt.All([x], smt.And(x > 0, x < 100), smt.And(silly_inc(x) == x + 1, silly_inc(x) <= 101)).sexpr())
    # difference is that contract has a trigger on it.
    assert silly_inc.contract.thm.body().eq(smt.All([x], smt.And(x > 0, x < 100), smt.And(silly_inc(x) == x + 1, silly_inc(x) <= 101)).body())