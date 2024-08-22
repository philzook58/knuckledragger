import pytest
import knuckledragger.smt as smt

import knuckledragger as kd
import knuckledragger.theories.Nat
import knuckledragger.theories.Int
import knuckledragger.theories.Real as R
import knuckledragger.theories.Complex as C
import knuckledragger.theories.Vec as Vec

if smt.solver != smt.VAMPIRESOLVER:
    import knuckledragger.theories.Interval

import knuckledragger.theories.Seq as ThSeq

from knuckledragger import Calc
import knuckledragger.utils


def test_true_infer():
    kd.lemma(smt.BoolVal(True))


def test_false_infer():
    with pytest.raises(Exception) as _:
        kd.lemma(smt.BoolVal(False))


def test_explosion():
    a = kd.axiom(smt.BoolVal(False), "False axiom")
    with pytest.raises(Exception) as _:
        kd.lemma(smt.BoolVal(True), by=[a])


def test_calc():
    x, y, z = smt.Ints("x y z")
    l1 = kd.axiom(x == y)
    l2 = kd.axiom(y == z)
    Calc([], x).eq(y, by=[l1]).eq(z, by=[l2]).qed()


def test_tptp():
    x = smt.Int("x")
    assert smt.And(x > 4, x <= 7).tptp() == "($greater(x,4) & $lesseq(x,7))"
    assert smt.IntSort().tptp() == "$int"
    assert smt.BoolSort().tptp() == "$o"
    assert (
        smt.ArraySort(
            smt.ArraySort(smt.BoolSort(), smt.IntSort()), smt.IntSort()
        ).tptp()
        == "(($o > $int) > $int)"
    )


def test_datatype():
    Foo = smt.Datatype("Foo")
    Foo.declare("foo", ("bar", smt.IntSort()), ("baz", smt.BoolSort()))
    Foo = Foo.create()
    x = Foo.foo(1, True)
    assert smt.simplify(x.bar).eq(smt.IntVal(1))
    assert smt.simplify(x.baz).eq(smt.BoolVal(True))


def test_qforall():
    x, y = smt.Reals("x y")
    assert kd.QForAll([x], x > 0).eq(smt.ForAll([x], x > 0))
    assert kd.QForAll([x], x == 10, x == 14, x > 0).eq(
        smt.ForAll([x], smt.Implies(smt.And(x == 10, x == 14), x > 0))
    )
    assert kd.QForAll([x, y], x > 0, y > 0).eq(
        smt.ForAll([x, y], smt.Implies(x > 0, y > 0))
    )
    Nat = kd.theories.Int.Nat
    x = smt.Const("x", Nat)
    assert kd.QForAll([x], x == Nat.mk(14)).eq(
        smt.ForAll([x], smt.Implies(x.wf(), x == Nat.mk(14)))
    )


def test_simp():
    assert kd.utils.simp(R.max(8, R.max(3, 4))).eq(smt.RealVal(8))
    assert kd.utils.simp2(R.max(8, R.max(3, 4))).eq(smt.RealVal(8))


def test_record():
    foo = kd.notation.Record("foo", ("bar", smt.IntSort()), ("baz", smt.BoolSort()))
    assert smt.simplify(foo.mk(1, True).bar).eq(smt.IntVal(1))


def test_seq():
    ThSeq.induct(smt.IntSort(), lambda x: x == x)


def test_cons():
    c = kd.notation.Cond()
    assert (
        c.when(smt.BoolVal(True))
        .then(smt.IntVal(1))
        .otherwise(smt.IntVal(2))
        .eq(smt.If(smt.BoolVal(True), smt.IntVal(1), smt.IntVal(2)))
    )
    c = kd.notation.Cond()
    assert (
        c.when(smt.BoolVal(True))
        .then(smt.IntVal(1))
        .when(smt.BoolVal(False))
        .then(smt.Int("y"))
        .otherwise(smt.IntVal(2))
        .eq(
            smt.If(
                smt.BoolVal(True),
                smt.IntVal(1),
                smt.If(smt.BoolVal(False), smt.Int("y"), smt.IntVal(2)),
            )
        )
    )


def test_match():
    x, y, z = smt.Reals("x y z")
    Var = smt.Var
    R = smt.RealSort()
    assert kd.utils.z3_match(x, Var(0, R)) == {Var(0, R): x}
    assert kd.utils.z3_match(x + y, Var(0, R) + Var(1, R)) == {
        Var(0, R): x,
        Var(1, R): y,
    }
    assert kd.utils.z3_match(x + y, Var(0, R) + Var(0, R)) == None
    assert kd.utils.z3_match(x + y + x, Var(0, R) + Var(1, R) + Var(0, R)) == {
        Var(0, R): x,
        Var(1, R): y,
    }
    assert kd.utils.z3_match(x + y + x * 6, Var(0, R) + Var(1, R) + Var(2, R)) == {
        Var(0, R): x,
        Var(1, R): y,
        Var(2, R): x * 6,
    }
    assert kd.utils.z3_match(
        x + y + x * 6 == 0, smt.ForAll([x, y, z], x + y + z == 0)
    ) == {
        Var(2, R): x,
        Var(1, R): y,
        Var(0, R): x * 6,
    }


def test_subterms():
    x, y = smt.Ints("x y")
    assert set(kd.utils.subterms(x + y + x)) == {x, y, x, x + y, x + y + x}


def test_pred():
    Even = kd.Record(
        "Even", ("val", kd.Z), ("div2", kd.Z), pred=lambda x: 2 * x.div2 == x.val
    )
    kd.lemma(Even(0, 0).wf())
