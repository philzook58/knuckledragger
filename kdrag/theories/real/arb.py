import kdrag as kd
import kdrag.smt as smt
import kdrag.theories.real as real
import operator as op
import flint
from typing import TypeAlias

Arb: TypeAlias = object

arb = flint.arb  # type: ignore
a, b = smt.Reals("a b")
flint_decls = {
    real.sqrt: arb.sqrt,
    real.sqr: lambda x: x**2,
    real.exp: arb.exp,
    real.ln: arb.log,
    real.sin: arb.sin,
    real.cos: arb.cos,
    real.tan: arb.tan,
    real.atan: arb.atan,
    real.pow: lambda x, y: x**y,
    real.pi.decl(): arb.pi,
    (a + b).decl(): op.add,
    (a * b).decl(): op.mul,
    (a / b).decl(): op.truediv,
    (a - b).decl(): op.sub,
    (a**b).decl(): op.pow,
}


def interp_flint(e: smt.ArithRef, env) -> flint.types.arb.arb:  # type: ignore
    """
    Interpret a z3 expression into an arb calculation.

    >>> interp_flint(real.pi, {})
    [3.14159265358979 +/- 3.34e-15]
    """
    if isinstance(e, int) or isinstance(e, float):
        return arb(e)
    if e in env:
        return env[e]
    elif smt.is_select(e) and e.arg(0) in flint_decls:
        return flint_decls[e.arg(0)](
            *[interp_flint(arg, env) for arg in e.children()[1:]]
        )
    elif smt.is_rational_value(e) and isinstance(e, smt.RatNumRef):
        return arb(e.numerator_as_long()) / arb(e.denominator_as_long())
    elif smt.is_app(e) and e.decl() in flint_decls:
        decl = e.decl()
        return flint_decls[decl](*[interp_flint(arg, env) for arg in e.children()])
    assert False, f"Can't interpret {e} into flint"


def arb_over_of_mid_rad(mid: smt.ArithRef, rad: smt.ArithRef) -> flint.types.arb.arb:  # type: ignore
    """
    Get overapproximating arb from midpoint and radius.

    >>> arb_over_of_mid_rad(1, 0)
    1.00000000000000
    >>> arb_over_of_mid_rad(1, 0.0005)
    [1.000 +/- 5.01e-4]
    """
    return arb(interp_flint(mid, {}), interp_flint(rad, {}))


def flint_eq_ax_unsafe(lhs, rhs):
    """
    This axiom schema is fishy, in that even if arb is implement correctly, this check does not assure the equality of the
    left and right hand side.
    but it is better than nothing.

    >>> flint_eq_ax_unsafe(real.pi, 4*real.atan(1))
    |= pi == 4*atan(1)
    >>> flint_eq_ax_unsafe(smt.RealVal(0), real.sin(0))
    |= 0 == sin(0)
    >>> flint_eq_ax_unsafe(real.sin(3*real.pi/2), -1)
    |= sin((3*pi)/2) == -1
    """
    if not interp_flint(lhs, {}).overlaps(interp_flint(rhs, {})):
        raise ValueError(f"lhs and rhs do not numerically overlap: {lhs} and {rhs}")
    return kd.axiom(smt.Eq(lhs, rhs), by="flint")


def arb_lt_ax(lhs: smt.ArithRef, rhs: smt.ArithRef) -> kd.kernel.Proof:
    """
    Use numerical evaluation to confirm ball of lhs is completely below ball of rhs

    >>> arb_lt_ax(3.14, real.pi)
    |= 157/50 < pi
    """
    if isinstance(lhs, int) or isinstance(lhs, float):
        lhs = smt.RealVal(
            lhs
        )  # We do this so that `<` overloading doesn't flip the direction, which is annoying
    if interp_flint(lhs, {}) < (interp_flint(rhs, {})):
        return kd.axiom(lhs < rhs, by="flint")  # type: ignore
    else:
        raise ValueError(
            f"{lhs} is not numerically strictly less than {rhs}",
            interp_flint(lhs, {}),
            interp_flint(rhs, {}),
        )


def arb_le_ax(lhs0: smt.ArithRef, rhs: smt.ArithRef) -> kd.kernel.Proof:
    """

    >>> arb_le_ax(3.14, real.pi)
    |= 157/50 <= pi
    >>> arb_le_ax(1,1)
    |= 1 <= 1
    """
    if isinstance(lhs0, int) or isinstance(lhs0, float):
        lhs: smt.ArithRef = smt.RealVal(
            lhs0
        )  # We do this so that `<` overloading doesn't flip the direction, which is annoying
    elif isinstance(lhs0, smt.ArithRef):
        lhs = lhs0
    else:
        raise ValueError("lhs must be a number or z3 expression", lhs0)
    if interp_flint(lhs, {}) <= (interp_flint(rhs, {})):
        return kd.axiom(lhs <= rhs, by="flint")  # type: ignore
    else:
        raise ValueError(
            f"{lhs} ball is not numerically less than {rhs} ball",
            interp_flint(lhs, {}),
            interp_flint(rhs, {}),
        )


def arb_gt(lhs, rhs):
    kd.prove(lhs > rhs, by=[arb_lt_ax(rhs, lhs)])


def arb_ge(lhs, rhs):
    kd.prove(lhs >= rhs, by=[arb_le_ax(rhs, lhs)])


def sin_bnd(x: Arb) -> kd.kernel.Proof:
    """
    >>> sin_bnd(arb(0))
    |= ForAll(x,
        Implies(And(0 - 0 <= x, x <= 0 + 0),
                And(0 - 0 <= sin(x), sin(x) <= 0 + 0)))
    >>> kd.prove(real.sin(0) <= 2, by=[sin_bnd(arb(0,0.1))(smt.RealVal(0))])
    |= sin(0) <= 2
    >>> kd.prove(real.sin(3.14) <= 0.02, by=[sin_bnd(arb(3.14, 0.01))])
    |= sin(157/50) <= 1/50
    """
    xm, xr = z3_mid_rad_of_arb(x)
    smid, sr = z3_mid_rad_of_arb(arb.sin(x))
    z3x = smt.Real("x")
    return kd.axiom(
        kd.QForAll(
            [z3x],
            xm - xr <= z3x,
            z3x <= xm + xr,
            smt.And(smid - sr <= real.sin(z3x), real.sin(z3x) <= smid + sr),
        ),
        by="flint",
    )


def arb_bnd(arbf, z3f):
    """
    >>> kd.prove(real.cos(0) == 1, by=[cos_bnd(arb(0))])
    |= cos(0) == 1
    """

    def res(x: Arb) -> kd.kernel.Proof:
        xm, xr = z3_mid_rad_of_arb(x)
        smid, sr = z3_mid_rad_of_arb(arbf(x))
        z3x = smt.Real("x")
        return kd.axiom(
            kd.QForAll(
                [z3x],
                xm - xr <= z3x,
                z3x <= xm + xr,
                smt.And(smid - sr <= z3f(z3x), z3f(z3x) <= smid + sr),
            ),
            by="flint",
        )

    return res


cos_bnd = arb_bnd(arb.cos, real.cos)
exp_bnd = arb_bnd(arb.exp, real.exp)
tan_bnd = arb_bnd(arb.tan, real.tan)
"""
This is probably the purest form of the information that arb offers.
In principle, larger scale rules can be derived from this.
"""


def z3_of_exact_arb(x: flint.arb) -> smt.ArithRef:  # type: ignore
    """
    Get exact arb as z3 value

    >>> z3_of_exact_arb(arb(1))
    1
    >>> z3_of_exact_arb(arb(1) + arb(2))
    3
    >>> z3_of_exact_arb(arb(2**1000))
    2**1000

    """
    if not x.is_finite():
        raise ValueError("Infinite value in z3_of_exact")
    elif not x.is_exact():
        raise ValueError("Not exact value in z3_of_exact", x)
    man, exp = x.man_exp()
    return smt.simplify(smt.RealVal(int(man)) * smt.RealVal(2) ** smt.RealVal(int(exp)))


def z3_mid_rad_of_arb(x: flint.arb) -> tuple[smt.ArithRef, smt.ArithRef]:  # type: ignore
    """
    Get midpoint and radius as z3 values.

    >>> z3_mid_rad_of_arb(arb(1))
    (1, 0)
    >>> z3_mid_rad_of_arb(arb(1) + arb(2))
    (3, 0)
    """
    if not x.is_finite():
        raise ValueError("Infinite value in z3_of_arb", x)
    """
    mid = x.mid().str(100, more=True, radius=True)
    rad = x.rad().str(100, more=True, radius=True)
    # +/- does not appear if matches arb exactly
    if "+/-" in mid or "+/-" in rad:
        raise ValueError("Unexpected error in conversion from arb to z3", mid, rad)
    """
    man, mid = x.mid().man_exp()  # m * 2**b
    return z3_of_exact_arb(x.mid()), z3_of_exact_arb(x.rad())


def bounds(e: smt.ArithRef) -> tuple[smt.ArithRef, smt.ArithRef]:
    """
    Get the bounds of a z3 expression.
    >>> bounds(1)
    (1, 1)
    >>> bounds(smt.RealVal(1) + smt.RealVal(2))
    (3, 3)
    """
    if isinstance(e, int) or isinstance(e, float):
        e = smt.RealVal(e)
    if not smt.is_real(e):
        raise ValueError("Not a real value", e)
    mid, rad = z3_mid_rad_of_arb(interp_flint(e, {}))
    return smt.simplify(mid - rad), smt.simplify(mid + rad)


def bound_ax(e: smt.ArithRef) -> kd.kernel.Proof:
    lower, upper = bounds(e)
    return kd.axiom(smt.And(lower <= e, e <= upper), by="flint_bnd")


def flint_bnd(t: smt.ArithRef, env) -> kd.kernel.Proof:
    # TODO: Maybe get rid of this?
    assert smt.is_real(t)
    assert all(smt.is_real(k) and isinstance(v, arb) for k, v in env.items())
    preconds = [smt.BoolVal(True)]
    for k, v in env.items():
        mid, rad = z3_mid_rad_of_arb(v)
        preconds.append(mid - rad <= k)
        preconds.append(k <= mid + rad)
    v = interp_flint(t, env)
    if not v.is_finite():
        raise ValueError("Infinite value in flint_bnd", t, env, v)
    mid, rad = z3_mid_rad_of_arb(v)
    if len(env) > 0:
        return kd.axiom(
            kd.QForAll(
                list(env.keys()), smt.And(preconds), mid - rad <= t, t <= mid + rad
            ),
            by="flint_eval",
        )
    else:
        return kd.axiom(smt.And(mid - rad <= t, t <= mid + rad), by="flint_eval")
