import kdrag as kd
from kdrag.theories.real import *
import kdrag.smt as smt
import kdrag.solvers as solvers


def test_abstract():
    x, y, z = smt.Reals("x y z")
    assert abstract_arith(x + y).eq(add(x, y))

    """
    kd.lemma(
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
    _1 = kd.kernel.lemma(
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
    # kd.lemma(has_lim(const(0), 0, 0), by=[has_lim.defn, const.defn, abs.defn])
    eps, delta, x = smt.Reals("eps delta x")
    const0_lim = kd.lemma(
        has_lim_mod(const(0), 0, 0, const(1)),
        by=[has_lim_mod.defn, const.defn, abs.defn],
    )
    kd.lemma(has_lim(const(0), 0, 0), by=[has_lim_seal, const0_lim])
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
