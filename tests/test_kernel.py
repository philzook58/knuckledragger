import pytest
import kdrag.smt as smt

import kdrag as kd
import kdrag.theories.nat
import kdrag.theories.int
import kdrag.theories.real as R
import kdrag.theories.bitvec as bitvec
import kdrag.theories.real.complex as complex
import kdrag.theories.algebra.group as group
import kdrag.theories as datatypes
import re

if smt.solver != smt.VAMPIRESOLVER:
    import kdrag.theories.real.interval

import kdrag.theories.seq as seq

from kdrag import Calc
import kdrag.utils as utils


def test_true_infer():
    kd.prove(smt.BoolVal(True))


def test_false_infer():
    with pytest.raises(Exception) as _:
        kd.kernel.prove(smt.BoolVal(False))



def test_explosion():
    a = kd.axiom(smt.BoolVal(False), "False axiom")
    with pytest.raises(Exception) as _:
        kd.prove(smt.BoolVal(True), by=[a])


def test_calc():
    x, y, z = smt.Ints("x y z")
    l1 = kd.axiom(x == y)
    l2 = kd.axiom(y == z)
    Calc([], x).eq(y, by=[l1]).eq(z, by=[l2]).qed()


def test_skolem():
    x, y = smt.Ints("x y")
    z = smt.Real("z")

    thm = smt.Exists([x, y, z], smt.And(x == x, y == y, z == z))
    pf = kd.kernel.prove(thm)
    vs, pf1 = kd.kernel.skolem(pf)
    print(vs, pf1)
    assert smt.Exists(vs, pf1.thm).body().eq(thm.body())

    thm = smt.ForAll([x, y, z], smt.And(x == x, y == y, z == z))
    pf = kd.kernel.prove(thm)
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
    foo = kd.Struct("foo", ("bar", smt.IntSort()), ("baz", smt.BoolSort()))
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
    l.have(x != x + 1)
    l.assumption()
    l.qed()

    p, q, r = smt.Bools("p q r")
    l = kd.tactics.Lemma(smt.Implies(p, p))
    l.qed()

    l = kd.tactics.Lemma(kd.QForAll([p, q], p, q, p))
    p1, q1 = l.intros()
    l.intros()
    l.cases(p1)
    l.auto()
    l.auto()
    l.qed()

    y = smt.Int("y")
    l = kd.tactics.Lemma(smt.Exists([x, y], smt.And(x == 2, y == 3)))
    l.exists(smt.IntVal(2), smt.IntVal(3))
    l.auto()
    l.qed()

    x, y, z = smt.Ints("x y z")
    P = smt.Function("P", smt.IntSort(), smt.BoolSort())
    myax = kd.axiom(smt.ForAll([z], P(z)))
    l = kd.tactics.Lemma(kd.QForAll([x], P(x)))
    x1 = l.intros()
    l.apply(myax)
    l.qed()

    p, q = smt.Bools("p q")
    l = kd.Lemma(smt.Implies(p, smt.Or(p, q)))
    l.intros()
    l.left()
    l.auto()
    l.qed()

    l = kd.Lemma(smt.Implies(q, smt.Or(p, p, p, q, p)))
    l.intros()
    l.left(3)
    l.auto()
    l.qed()

    l = kd.Lemma(smt.Implies(p, smt.Or(q, q, q, p)))
    l.intros()
    l.right()
    l.qed()

    x = smt.Int("x")
    sqr = kd.define("sqr", [x], x * x)
    l = kd.Lemma(smt.ForAll([x], sqr(x) == x * x))
    l.intros()
    l.unfold(sqr)
    print(l)
    l.auto()
    l.qed()
    l = kd.Lemma(smt.ForAll([x], sqr(sqr(x)) == x * x * x * x))
    l.intros()
    l.unfold(sqr)
    l.unfold(sqr)
    l.auto()
    l.qed()

    x, y = smt.Ints("x y")
    even = kd.define("even", [x], smt.Exists([y], x == 2 * y))
    odd = kd.define("odd", [x], smt.Exists([y], x == 2 * y + 1))

    evdef2 = kd.kernel.prove(
        smt.ForAll([x], even(x) == smt.Exists([y], x == 2 * y)), by=[even.defn]
    )
    l = kd.Lemma(kd.QForAll([x], even(x), even(x + 2)))
    x1 = l.intros()
    l.intros()
    l.apply(even.defn)
    l.rewrite(even.defn, at=0)
    y1 = l.einstan(0)
    l.exists(y1 + 1)
    l.auto()
    l.qed()
    # kd.kernel.prove(kd.QForAll([x], even(x), even(x+2)), by=[even.defn])
    # l.exists(y1 + 1)
    # evdef2.thm.body()

    l = kd.Lemma(kd.QForAll([x], even(x), even(x + 2)))
    [
        x1 := l.intros(),
        l.intros(),
        l.apply(even.defn),
        l.rewrite(even.defn, at=0),
        y1 := l.einstan(0),
        l.exists(y1 + 1),
        l.auto(),
    ]
    l.qed()

    IntList = smt.Datatype("IntList")
    IntList.declare("nil")
    IntList.declare("cons", ("car", smt.IntSort()), ("cdr", IntList))
    IntList = IntList.create()

    x, y = smt.Consts("x y", IntList)
    z = smt.Int("z")

    l = kd.prove(
        smt.ForAll(
            [x], smt.Or(x == IntList.nil, smt.Exists([y, z], x == IntList.cons(z, y)))
        )
    )
    l = kd.Lemma(
        smt.ForAll(
            [x], smt.Or(x == IntList.nil, smt.Exists([z, y], x == IntList.cons(z, y)))
        )
    )
    [
        x1 := l.fix(),
        l.cases(x1),
        [l.left(), l.auto()],
        [l.right(), l.exists(x1.car, x1.cdr), l.auto()],
    ]
    l.qed()


def test_eq():
    x, y = smt.Ints("x y")
    assert smt.Eq(smt.IntVal(2) + smt.IntVal(3), smt.IntVal(5)).arg(1).eq(smt.IntVal(5))
    assert smt.Eq((x >= 14), smt.Exists([y], x == 2 * y)).arg(0).eq(x >= 14)
    assert smt.Eq((x >= 14), x >= 13).arg(0).eq(x >= 14)


def test_pred():
    Even = kd.Struct(
        "Even",
        ("val", kd.Z),
        ("div2", kd.Z),
        pred=lambda x: 2 * x.div2 == x.val,
    )
    kd.prove(Even(0, 0).wf())


def test_induct():
    List = smt.Datatype("List")
    List.declare("nil")
    List.declare("cons", ("head", smt.IntSort()), ("tail", List))
    List = List.create()
    x = smt.Const("x", List)
    assert (
        kd.kernel.induct_inductive(x, smt.Lambda([x], smt.BoolVal(True))) is not None
    )


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
        smt.Eq(t[smt.IntVal(42)], smt.IntVal(42))
    )


def test_lambda_def():
    # test that the lambda has been removed by the definition mechanism
    x, y = smt.Ints("x y")
    z, w = smt.Bools("z w")
    test = kd.define("test", [x], smt.Lambda([x], x), lift_lambda=True)
    assert test.defn.thm.body().eq(smt.ForAll([x, y], test(x)[y] == y).body())


"""
This is causing failure in vampire becausei tdoesn't support multiarity array
def test_lambda_2():
    

    test = kd.define("test2", [], smt.Lambda([z, x], z))
    # print("body", test.defn.thm.body())
    # print("ax", smt.ForAll([z, x], test[z, x] == z).body())
    assert test.defn.thm.body().eq(smt.ForAll([z, x], test[z, x] == z).body())
    # print(smt.ForAll([y, x, z, w], test(y, x)[z, w] == x + y).body())
    # print(test.defn.thm.body())
    # assert test.defn.thm.body().eq(
    #    smt.ForAll([y, x, z, w], test(y, x)[z, w] == x + y).body()
    # )
"""


def test_bv():
    bv8 = bitvec.BVTheory(8)


def test_forget():
    x, y = smt.Ints("x y")
    assert kd.kernel.forget2(
        [smt.IntVal(2), smt.IntVal(3)], smt.Exists([x, y], smt.And(x == 2, y == 3))
    ).thm.eq(
        smt.Implies(
            smt.And(smt.IntVal(2) == 2, smt.IntVal(3) == 3),
            smt.Exists([x, y], smt.And(x == 2, y == 3)),
        )
    )

def test_no_mix_keyword():
    Point = kd.Struct("Point", ("x", smt.IntSort()), ("y", smt.IntSort()))
    with pytest.raises(Exception) as _:
        Point(1,y=2)