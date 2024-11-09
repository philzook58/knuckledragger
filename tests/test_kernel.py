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


def test_tptp():
    x = smt.Int("x")
    assert (
        re.match(
            r"\(\$greater\(x_[0-9a-f]+,4\) & \$lesseq\(x_[0-9a-f]+,7\)\)",
            kd.utils.expr_to_tptp(smt.And(x > 4, x <= 7)),
        )
        is not None
    )
    assert kd.utils.sort_to_tptp(smt.IntSort()) == "$int"
    assert kd.utils.sort_to_tptp(smt.BoolSort()) == "$o"
    assert (
        kd.utils.sort_to_tptp(
            smt.ArraySort(smt.ArraySort(smt.BoolSort(), smt.IntSort()), smt.IntSort())
        )
        == "(($o > $int) > $int)"
    )


def test_fof():
    x = smt.Int("x")
    assert re.match(
        r"\(!\[X_(?P<var_num>[a-zA-Z0-9]+)\] : \(\$greater\(X_(?P=var_num),4\) & \$lesseq\(X_(?P=var_num),7\)\)\)",
        kd.utils.expr_to_tptp(smt.ForAll([x], smt.And(x > 4, x <= 7)), format="fof"),
    )


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


def test_simp():
    assert kd.utils.simp(R.max(8, R.max(3, 4))).eq(smt.RealVal(8))
    assert kd.utils.simp2(R.max(8, R.max(3, 4))).eq(smt.RealVal(8))


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


def test_match():
    x, y, z = smt.Reals("x y z")
    Var = smt.Var
    R = smt.RealSort()
    assert kd.utils.pmatch_db(x, Var(0, R)) == {Var(0, R): x}
    assert kd.utils.pmatch_db(x + y, Var(0, R) + Var(1, R)) == {
        Var(0, R): x,
        Var(1, R): y,
    }
    assert kd.utils.pmatch_db(x + y, Var(0, R) + Var(0, R)) == None
    assert kd.utils.pmatch_db(x + y + x, Var(0, R) + Var(1, R) + Var(0, R)) == {
        Var(0, R): x,
        Var(1, R): y,
    }
    assert kd.utils.pmatch_db(x + y + x * 6, Var(0, R) + Var(1, R) + Var(2, R)) == {
        Var(0, R): x,
        Var(1, R): y,
        Var(2, R): x * 6,
    }
    assert kd.utils.pmatch_db(
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


def test_generate():
    assert len(list(kd.utils.generate(smt.BitVecSort(2)))) == 4
    Foo = kd.NewType(
        "Foo", smt.IntSort(), pred=lambda x: smt.And(x.val >= 0, x.val < 10)
    )
    assert len(list(kd.utils.generate(Foo))) == 10


def test_bv():
    bv8 = bitvec.BVTheory(8)


def test_unify():
    x, y, z = (
        smt.Var(0, smt.IntSort()),
        smt.Var(1, smt.IntSort()),
        smt.Var(2, smt.IntSort()),
    )
    assert utils.unify_db(smt.IntVal(3), smt.IntVal(3)) == {}
    assert utils.unify_db(smt.IntVal(3), smt.IntVal(4)) == None
    assert utils.unify_db(x, smt.IntVal(3)) == {x: smt.IntVal(3)}
    assert utils.unify_db(x, y) == {x: y}
    assert utils.unify_db(x + x, y + y) == {x: y}
    assert utils.unify_db(x + x, y + z) == {x: y, z: y}
    assert utils.unify_db(x + y, y + z) == {x: z, y: z}
    assert utils.unify_db(y + z, x + y) == {y: x, z: x}
    # non terminating if no occurs check
    assert utils.unify_db((x + x) + x, x + (x + x)) == None
    assert utils.unify_db(1 + x, x) == None


def test_rewrite():
    x, y, z = smt.Reals("x y z")
    succ_0 = smt.ForAll([x], x + 0 == x)
    succ_0_rule = utils.rule_of_theorem(succ_0)
    vs, lhs, rhs = succ_0_rule
    assert utils.rewrite1(y + 0, vs, lhs, rhs).eq(y)
    t = (y + 0) + 0
    assert utils.rewrite(t, [succ_0_rule]).eq(y)
    assert utils.rewrite_star(t, [succ_0_rule]).eq(y)

    succ_0 = kd.lemma(succ_0)
    assert kd.tactics.simp(t, by=[succ_0]).thm.eq(t == y)
