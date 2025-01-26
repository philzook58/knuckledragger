import kdrag as kd
import kdrag.smt as smt

import kdrag.theories.real as real
import kdrag.utils as utils
import kdrag.rewrite as rewrite

def test_simp():
    assert rewrite.simp1(real.max(8, real.max(3, 4))).eq(smt.RealVal(8))
    assert rewrite.simp2(real.max(8, real.max(3, 4))).eq(smt.RealVal(8))


"""
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
"""


def test_pmatch():
    x, y, z = smt.Ints("x y z")
    F, G = smt.Consts("F G", smt.ArraySort(smt.IntSort(), smt.IntSort()))
    assert utils.pmatch([x], x, smt.IntVal(4)) == {x: smt.IntVal(4)}
    assert utils.pmatch([x], smt.IntVal(3), smt.IntVal(3)) == {}
    assert utils.pmatch([x], smt.IntVal(3), smt.IntVal(4)) == None
    assert utils.pmatch([x], x, smt.IntVal(3)) == {x: smt.IntVal(3)}
    assert utils.pmatch([x], x + x, smt.IntVal(3) + smt.IntVal(4)) == None
    assert utils.pmatch([x], x + x, smt.IntVal(3) + smt.IntVal(3)) == {x: smt.IntVal(3)}
    assert utils.pmatch([y], x + x, smt.IntVal(3) + smt.IntVal(3)) == None
    assert utils.pmatch([x, y], x + y, smt.IntVal(3) + smt.IntVal(4)) == {
        x: smt.IntVal(3),
        y: smt.IntVal(4),
    }

    # alpha equiv terms should utils.pmatch
    assert utils.pmatch([], smt.Lambda([x], x == x), smt.Lambda([y], y == y)) == {}
    t = smt.Lambda([x, y], x + y)
    vs, body = utils.open_binder(t)
    assert utils.pmatch([], t, smt.Lambda(vs, body)) == {}

    assert utils.alpha_eq(
        utils.pmatch([F], smt.Lambda([x], F[x]), smt.Lambda([x], x + 3))[F],
        smt.Lambda([x], x + 3),
    )
    assert utils.alpha_eq(
        utils.pmatch([F], smt.Lambda([x], F[x]), smt.Lambda([y], y + 3))[F],
        smt.Lambda([z], z + 3),
    )
    assert utils.alpha_eq(
        utils.pmatch([F], smt.Lambda([x], F[x]), smt.Lambda([x], G[x]))[F],
        smt.Lambda([x], G[x]),
    )

    # Failing examples
    # should we allow this?
    # utils.pmatch([F], F[3], G[3]). Seems obvious what the answer should be {F:G}, but we're opening up a can of worms

    assert (
        utils.pmatch(
            [F], smt.Lambda([x, y], F), smt.Lambda([x, y], smt.Lambda([z], x + 3))
        )
        == None
    )

    # This is the sort of thing you have to do if you want to apply an induction principle about (forall P) to a goal.
    P = smt.Const("P", smt.ArraySort(smt.IntSort(), smt.BoolSort()))
    assert utils.alpha_eq(
        utils.pmatch(
            [P], smt.ForAll([x], P[x]), smt.ForAll([y], smt.Or(y == 0, y > 0))
        )[P],
        smt.Lambda([z], smt.Or(z == 0, z > 0)),
    )

    assert (
        utils.pmatch([F, G], smt.Lambda([x, y], F[y] + F[y]), smt.Lambda([x, y], x + y))
        == None
    )
    assert (
        utils.pmatch([F, G], smt.Lambda([x, y], F[y] + F[x]), smt.Lambda([x, y], x + y))
        == None
    )
    assert utils.alpha_eq(
        utils.pmatch(
            [F, G], smt.Lambda([x, y], F[x] + F[y]), smt.Lambda([x, y], x + y)
        )[F],
        smt.Lambda([x], x),
    )


def test_pmatch2():
    x, y, z = smt.Ints("x y z")
    F, G = smt.Consts("F G", smt.ArraySort(smt.IntSort(), smt.IntSort()))
    assert utils.pmatch([F], smt.Lambda([x, y], F[x]), smt.Lambda([x, y], G[y])) == None


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
    succ_0_rule = rewrite.rule_of_theorem(succ_0)
    vs, lhs, rhs = succ_0_rule
    assert rewrite.rewrite1(y + 0, vs, lhs, rhs).eq(y)
    t = (y + 0) + 0
    assert rewrite.rewrite(t, [succ_0_rule]).eq(y)
    assert rewrite.rewrite_star(t, [succ_0_rule]).eq(y)

    succ_0 = kd.prove(succ_0)
    assert kd.tactics.simp(t, by=[succ_0]).thm.eq(t == y)


def test_apply():
    x, y, z = smt.Reals("x y z")
    path = smt.Function("path", smt.RealSort(), smt.RealSort(), smt.BoolSort())
    edge = smt.Function("edge", smt.RealSort(), smt.RealSort(), smt.BoolSort())
    head = path(x, z)
    body = smt.And(path(x, y), edge(y, z))
    assert rewrite.apply(path(1, 3), [x, y, z], head, body).eq(
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


def test_lpo():
    x, y, z, e = smt.Ints("x y z e")
    assert rewrite.lpo([x], x, x) == rewrite.Order.EQ
    assert rewrite.lpo([y], x, x) == rewrite.Order.EQ
    assert rewrite.lpo([x], x, y) == rewrite.Order.NGE
    assert rewrite.lpo([x, y], x, y) == rewrite.Order.NGE
    assert rewrite.lpo([x], x, y) == rewrite.Order.NGE
    assert rewrite.lpo([], y, x) == rewrite.Order.GR
    assert rewrite.lpo([], x, y) == rewrite.Order.NGE
    assert rewrite.lpo([], x + y, x) == rewrite.Order.GR
    assert rewrite.lpo([x], x + y, y) == rewrite.Order.GR
    f = smt.Function("f", smt.IntSort(), smt.IntSort(), smt.IntSort())
    i = smt.Function("i", smt.IntSort(), smt.IntSort())
    assert rewrite.lpo([x], f(x, e), x) == rewrite.Order.GR
    assert rewrite.lpo([x], y + x, x) == rewrite.Order.GR
    assert rewrite.lpo([x, y], y + x, x) == rewrite.Order.GR
    assert rewrite.lpo([], f(x, x), x) == rewrite.Order.GR
    assert rewrite.lpo([], x, f(x, x)) == rewrite.Order.NGE
    assert rewrite.lpo([], i(e), e) == rewrite.Order.GR
    assert rewrite.lpo([x, y], i(f(x, y)), f(i(x), i(y))) == rewrite.Order.GR
    assert rewrite.lpo([x, y, z], f(f(x, y), z), f(x, f(y, z))) == rewrite.Order.GR
    assert rewrite.lpo([x, y, z], f(x, f(y, z)), f(f(x, y), z)) == rewrite.Order.NGE


def test_kbo():
    x, y, z, e = smt.Ints("x y z e")
    assert rewrite.kbo([x], x, x) == rewrite.Order.EQ
    assert rewrite.kbo([y], x, x) == rewrite.Order.EQ
    assert rewrite.kbo([x], x, y) == rewrite.Order.NGE
    assert rewrite.kbo([x, y], x, y) == rewrite.Order.NGE
    assert rewrite.kbo([x], x, y) == rewrite.Order.NGE
    assert rewrite.kbo([], y, x) == rewrite.Order.GR
    assert rewrite.kbo([], x, y) == rewrite.Order.NGE
    assert rewrite.kbo([], x + y, x) == rewrite.Order.GR
    assert rewrite.kbo([x], x + y, y) == rewrite.Order.GR
    f = smt.Function("f", smt.IntSort(), smt.IntSort(), smt.IntSort())
    i = smt.Function("i", smt.IntSort(), smt.IntSort())
    assert rewrite.kbo([x], f(x, e), x) == rewrite.Order.GR
    assert rewrite.kbo([x], y + x, x) == rewrite.Order.GR
    assert rewrite.kbo([x, y], y + x, x) == rewrite.Order.GR
    assert rewrite.kbo([], f(x, x), x) == rewrite.Order.GR
    assert rewrite.kbo([], x, f(x, x)) == rewrite.Order.NGE
    assert rewrite.kbo([], i(e), e) == rewrite.Order.GR
    assert rewrite.kbo([x, y], f(i(x), i(y)), i(f(x, y))) == rewrite.Order.GR
    assert rewrite.kbo([x, y, z], f(f(x, y), z), f(x, f(y, z))) == rewrite.Order.GR
    assert rewrite.kbo([x, y, z], f(x, f(y, z)), f(f(x, y), z)) == rewrite.Order.NGE
