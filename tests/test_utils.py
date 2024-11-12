import kdrag as kd
import kdrag.smt as smt

import kdrag.theories.real as real
import kdrag.utils as utils


def test_simp():
    assert kd.utils.simp(real.max(8, real.max(3, 4))).eq(smt.RealVal(8))
    assert kd.utils.simp2(real.max(8, real.max(3, 4))).eq(smt.RealVal(8))


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


def test_generate():
    assert len(list(kd.utils.generate(smt.BitVecSort(2)))) == 4
    Foo = kd.NewType(
        "Foo", smt.IntSort(), pred=lambda x: smt.And(x.val >= 0, x.val < 10)
    )
    assert len(list(kd.utils.generate(Foo))) == 10


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


def test_apply():
    x, y, z = smt.Reals("x y z")
    path = smt.Function("path", smt.RealSort(), smt.RealSort(), smt.BoolSort())
    edge = smt.Function("edge", smt.RealSort(), smt.RealSort(), smt.BoolSort())
    head = path(x, z)
    body = smt.And(path(x, y), edge(y, z))
    assert utils.apply(path(1, 3), [x, y, z], head, body).eq(
        smt.And(path(1, y), edge(y, 3))
    )


def test_alpha_eq():
    x, y = smt.Reals("x y")
    z = smt.Int("z")
    assert utils.alpha_eq(smt.Lambda([x], x), smt.Lambda([y], y))
    assert not utils.alpha_eq(smt.ForAll([x], x == x), smt.Exists([y], y == y))
    t = smt.Lambda([x, y], x + y)
    vs, body = utils.open_binder(t)
    assert utils.alpha_eq(t, smt.Lambda(vs, body))
    t = smt.Lambda([x, z], x + z)
    vs, body = utils.open_binder(t)
    assert utils.alpha_eq(t, smt.Lambda(vs, body))
    assert utils.alpha_eq(smt.RealVal(1), smt.RealVal(1))
    assert not utils.alpha_eq(smt.RealVal(1), smt.RealVal(2))
    assert not utils.alpha_eq(smt.RealVal(1), smt.IntVal(1))
    assert not utils.alpha_eq(smt.BoolVal(True), smt.ForAll([x], x == x))


"""
def test_factor():
    x, y, z = smt.Reals("x y z")
    print(utils.factor(x**2 + 2 * x + 1))
    print(utils.factor(x * y + x * z))
    assert utils.factor(x**2 + 2 * x + 1).eq((x + 1) ** 2)
"""
