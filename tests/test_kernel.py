import pytest
import kdrag.smt as smt

import kdrag as kd
import kdrag.theories.datatypes.nat
import kdrag.theories.int
import kdrag.theories.real as R
import kdrag.theories.bitvec as bitvec
import kdrag.theories.complex as complex
import kdrag.theories.algebra.group as group
import kdrag.theories.datatypes as datatypes
import re

if smt.solver != smt.VAMPIRESOLVER:
    import kdrag.theories.interval

import kdrag.theories.seq as seq

from kdrag import Calc
import kdrag.utils as utils


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


def test_skolem():
    x, y = smt.Ints("x y")
    z = smt.Real("z")

    thm = smt.Exists([x, y, z], smt.And(x == x, y == y, z == z))
    pf = kd.kernel.lemma(thm)
    vs, pf1 = kd.kernel.skolem(pf)
    print(vs, pf1)
    assert smt.Exists(vs, pf1.thm).body().eq(thm.body())

    thm = smt.ForAll([x, y, z], smt.And(x == x, y == y, z == z))
    pf = kd.kernel.lemma(thm)
    assert kd.kernel.instan(
        [smt.IntVal(3), smt.IntVal(4), smt.RealVal(5)], pf
    ).thm == smt.And(
        smt.IntVal(3) == smt.IntVal(3),
        smt.IntVal(4) == smt.IntVal(4),
        smt.RealVal(5) == smt.RealVal(5),
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
    NatI = kd.theories.int.NatI
    x = smt.Const("x", NatI)
    assert kd.QForAll([x], x == NatI.mk(14)).eq(
        smt.ForAll([x], smt.Implies(x.wf(), x == NatI.mk(14)))
    )


def test_record():
    foo = kd.notation.Record("foo", ("bar", smt.IntSort()), ("baz", smt.BoolSort()))
    assert smt.simplify(foo.mk(1, True).bar).eq(smt.IntVal(1))


def test_seq():
    seq.induct(smt.IntSort(), lambda x: x == x)
    seq.Seq(smt.IntSort())


"""
def test_cond():
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
"""


def test_cond():
    x = smt.Real("x")
    assert kd.cond(
        (x > 0, 3 * x), (x < 0, 2 * x), (x == 0, 5 * x), default=smt.Real("undefined")
    ).eq(
        smt.If(
            x > 0,
            3 * x,
            smt.If(x < 0, 2 * x, smt.If(x == 0, 5 * x, smt.Real("undefined"))),
        )
    )
    with pytest.raises(Exception) as _:
        kd.cond((x < 0, 2 * x), (x > 0, 3 * x))


def test_Lemma():
    x = smt.Int("x")
    l = kd.tactics.Lemma(x != x + 1)
    l.intro([smt.Int("x")])
    l.have(x != x + 1)
    l.qed()


def test_pred():
    Even = kd.Record(
        "Even", ("val", kd.Z), ("div2", kd.Z), pred=lambda x: 2 * x.div2 == x.val
    )
    kd.lemma(Even(0, 0).wf())


def test_induct():
    List = smt.Datatype("List")
    List.declare("nil")
    List.declare("cons", ("head", smt.IntSort()), ("tail", List))
    List = List.create()
    assert datatypes.induct(List) != None


# TODO: test unsound
# take each module and run z3 on it for 10 seconds. It better come back unknown


def test_beta():
    x = smt.Int("x")
    y = smt.Bool("y")
    t = smt.Lambda([x, y], x + 1)
    assert kd.kernel.beta_conv(t, smt.IntVal(3), smt.BoolVal(True)).thm.eq(
        t[smt.IntVal(3), smt.BoolVal(True)] == smt.IntVal(3) + smt.IntVal(1)
    )
    t = smt.Lambda([x], x)
    assert kd.kernel.beta_conv(t, smt.IntVal(42)).thm.eq(
        t[smt.IntVal(42)] == smt.IntVal(42)
    )


def test_lambda_def():
    # test that the lambda has been removed by the definition mechanism
    x, y = smt.Ints("x y")
    z, w = smt.Bools("z w")
    test = kd.define("test", [x], smt.Lambda([x], x))
    assert test.defn.thm.body().eq(smt.ForAll([x, y], test(x)[y] == y).body())

    test = kd.define("test2", [], smt.Lambda([z, x], z))
    # print("body", test.defn.thm.body())
    # print("ax", smt.ForAll([z, x], test[z, x] == z).body())
    assert test.defn.thm.body().eq(smt.ForAll([z, x], test[z, x] == z).body())
    # print(smt.ForAll([y, x, z, w], test(y, x)[z, w] == x + y).body())
    # print(test.defn.thm.body())
    # assert test.defn.thm.body().eq(
    #    smt.ForAll([y, x, z, w], test(y, x)[z, w] == x + y).body()
    # )


def test_bv():
    bv8 = bitvec.BVTheory(8)
