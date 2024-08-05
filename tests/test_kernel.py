import pytest
import z3

import knuckledragger as kd
import knuckledragger.theories.Nat
import knuckledragger.theories.Int
import knuckledragger.theories.Real as R
import knuckledragger.theories.Complex as C
import knuckledragger.theories.Interval

import knuckledragger.theories.Seq as ThSeq

from knuckledragger import Calc
import knuckledragger.utils


def test_true_infer():
    kd.lemma(z3.BoolVal(True))


def test_false_infer():
    with pytest.raises(Exception) as _:
        kd.lemma(z3.BoolVal(False))


def test_explosion():
    a = kd.axiom(z3.BoolVal(False), "False axiom")
    with pytest.raises(Exception) as _:
        kd.lemma(z3.BoolVal(True), by=[a])


def test_calc():
    x, y, z = z3.Ints("x y z")
    l1 = kd.axiom(x == y)
    l2 = kd.axiom(y == z)
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


def test_qforall():
    x, y = z3.Reals("x y")
    assert kd.QForAll([x], x > 0).eq(z3.ForAll([x], x > 0))
    assert kd.QForAll([x], x == 10, x == 14, x > 0).eq(
        z3.ForAll([x], z3.Implies(z3.And(x == 10, x == 14), x > 0))
    )
    assert kd.QForAll([x, y], x > 0, y > 0).eq(
        z3.ForAll([x, y], z3.Implies(x > 0, y > 0))
    )
    x.wf = x >= 0
    assert kd.QForAll([x], x == 14).eq(z3.ForAll([x], z3.Implies(x >= 0, x == 14)))


def test_simp():
    assert kd.utils.simp(R.max(8, R.max(3, 4))).eq(z3.RealVal(8))
    assert kd.utils.simp2(R.max(8, R.max(3, 4))).eq(z3.RealVal(8))


def test_record():
    foo = kd.notation.Record("foo", ("bar", z3.IntSort()), ("baz", z3.BoolSort()))
    assert z3.simplify(foo.mk(1, True).bar).eq(z3.IntVal(1))


def test_seq():
    ThSeq.induct(z3.IntSort(), lambda x: x == x)
