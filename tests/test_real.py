import kdrag as kd
from kdrag.theories.real import *
import kdrag.smt as smt
import kdrag.solvers as solvers
import kdrag.theories.real as real
import kdrag.theories.real.sympy


def test_abstract():
    x, y, z = smt.Reals("x y z")
    assert abstract_arith(x + y).eq(add(x, y))

    """
    kd.prove(
        deriv(ident() * ident()) == const(2) * ident(),
        by=[
            deriv_mul,
            deriv_ident,
            deriv_const,
            const.defn,
            ident.defn,
            fmul.defn,
            fadd.defn,
        ],
    )
    """


def test_deriv():
    x = smt.Real("x")
    c = kd.Calc([], deriv(X * X))
    c.eq(deriv(X) * X + X * deriv(X), by=[deriv_mul])
    c.eq(const(1) * X + X * const(1), by=[deriv_ident])
    """
    # c.eq(X + X * const(1), by=[const.defn, fmul.defn])
    _1 = kd.kernel.prove(
        const(1) * X + X * const(1) == X + X,
        by=[const.defn, fmul.defn],
        solver=solvers.VampireTHFSolver,
    )
    c.eq(X + X, by=[const.defn, _1, fmul.defn])
    c.eq(const(2) * X, by=[const.defn, fadd.defn, fmul.defn])
    derive_sq = c.qed()
    """


# disabled
def lim():
    # kd.prove(has_lim(const(0), 0, 0), by=[has_lim.defn, const.defn, abs.defn])
    eps, delta, x = smt.Reals("eps delta x")
    const0_lim = kd.prove(
        has_lim_mod(const(0), 0, 0, const(1)),
        by=[has_lim_mod.defn, const.defn, abs.defn],
    )
    kd.prove(has_lim(const(0), 0, 0), by=[has_lim_seal, const0_lim])
    """
    c = kd.Calc([], has_lim(const(0), 0, 0))
    c.eq(
        kd.QForAll(
            [eps],
            eps > 0,
            smt.Exists(
                [delta],
                kd.QForAll([x], abs(x - 0) < delta, abs(const(0)(x) - 0) < eps),
            ),
        ),
        by=[has_lim.defn],
    )
    """
    # l = kd.Lemma(has_lim(const(0), 0, 0))
    # l.fixes(eps)
    # l.


import flint


def test_flint():
    real.sympy.flint_bnd(real.pi, {})
    x = smt.Real("x")
    real.sympy.flint_bnd(real.sin(x), {x: flint.arb.pi()})
    assert (
        real.sympy.interp_flint(smt.RatVal(232, 1), {}).mid().str()
        == "232.000000000000"
    )
    kd.kernel.prove(
        kd.QForAll([x], -5 <= x, x <= 5, sin(x) <= 1),
        by=[real.sympy.flint_bnd(real.sin(x), {x: flint.arb(0, 10)})],
    )
    assert (
        "1.00000000000000e+100"
        in real.sympy.interp_flint(
            smt.RealVal(10**100),
            {},
        )
        .mid()
        .str()
    )


import sympy


def test_sympy():
    assert real.sympy.z3_of_sympy(real.sympy.interp_sympy(real.pi)).eq(real.pi)
    x, y, z = smt.Reals("x y z")
    sx, sy, sz = sympy.symbols("x y z")
    env = {x: sx, y: sy, z: sz}
    rev_env = {v: k for k, v in env.items()}

    def round_trip(e):
        assert real.sympy.z3_of_sympy(
            real.sympy.interp_sympy(e, env=env), env=rev_env
        ).eq(e)

    round_trip(x + y)
    round_trip(x * y)
    assert real.sympy.z3_of_sympy(
        real.sympy.interp_sympy(x - y, env=env), env=rev_env
    ).eq(x + -1 * y)
    assert real.sympy.z3_of_sympy(
        real.sympy.interp_sympy(x / y, env=env), env=rev_env
    ).eq(x * y**-1)
    # round_trip(real.sqrt(x))
    # assert real.sin == real.sin(x).decl()
    round_trip(real.sin(real.cos(real.exp(x))))


def test_sympy_manip():
    x, y, z = smt.Reals("x y z")
    assert real.sympy.factor([x], x**2 + 2 * x + 1).eq((1 + x) ** 2)
    assert real.sympy.factor([x], x**2 - 1).eq((1 + x) * (-1 + x))

    def ptree(e):
        if smt.is_app(e):
            return (e.decl().name(), [ptree(arg) for arg in e.children()])
        else:
            return e.sexpr()

    add = (x + y).decl()
    mul = (x * y).decl()
    assert real.sympy.expand([x], (1 + x) ** 2).eq(add(1, x**2, 2 * x))
    assert real.sympy.expand([x, y], x * (x + 2 * y)).eq(x**2 + mul(2, x, y))
    kd.kernel.prove(real.sympy.expand([x], (1 + x) ** 2) == 1 + 2 * x + x**2)


def test_vampire():
    pass
    # TODO: broken again
    # test vampire with more significxant set of features
    # kd.prove(smt.BoolVal(True), solver=solvers.VampireSolver)
