import pytest
from knuckledragger import lemma, axiom
import z3

import knuckledragger.theories.Nat
import knuckledragger.theories.Int
import knuckledragger.theories.Real

import knuckledragger.theories.List
import knuckledragger.theories.Seq

from knuckledragger.utils import Calc


def test_true_infer():
    lemma(z3.BoolVal(True))


def test_false_infer():
    with pytest.raises(Exception) as _:
        lemma(z3.BoolVal(False))


def test_explosion():
    a = axiom(z3.BoolVal(False), "False axiom")
    with pytest.raises(Exception) as _:
        lemma(z3.BoolVal(True), by=[a])


def test_calc():
    x, y, z = z3.Ints("x y z")
    l1 = axiom(x == y)
    l2 = axiom(y == z)
    Calc([], x).eq(y, by=[l1]).eq(z, by=[l2]).qed()


def test_tptp():
    x = z3.Int("x")
    assert z3.And(x > 4, x <= 7).tptp() == "($greater(x,4) & $lesseq(x,7))"
    assert z3.IntSort().tptp() == "$int"
    assert z3.BoolSort().tptp() == "$o"
    assert (
        z3.ArraySort(z3.ArraySort(z3.BoolSort(), z3.IntSort()), z3.IntSort()).tptp()
        == "(($o > $int) > $int)"
    )


def test_datatype():
    Foo = z3.Datatype("Foo")
    Foo.declare("foo", ("bar", z3.IntSort()), ("baz", z3.BoolSort()))
    Foo = Foo.create()
    x = Foo.foo(1, True)
    assert z3.simplify(x.bar).eq(z3.IntVal(1))
    assert z3.simplify(x.baz).eq(z3.BoolVal(True))
