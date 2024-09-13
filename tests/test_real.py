import kdrag as kd
from kdrag.theories.real import *
import kdrag.smt as smt


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
    c = kd.Calc([], deriv(X * X))
    c.eq(deriv(X) * X + X * deriv(X), by=[deriv_mul])
    c.eq(const(1) * X + X * const(1), by=[deriv_ident])
    c.eq(X + X, by=[const.defn, fmul.defn])
    c.eq(const(2) * X, by=[const.defn, fadd.defn, fmul.defn])
    derive_sq = c.qed()
