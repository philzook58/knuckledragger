import kdrag.theories.real as real
import kdrag as kd
import kdrag.smt as smt
import flint
import operator as op
import sympy

a, b = smt.Reals("a b")
flint_decls = {
    real.sqrt: flint.arb.sqrt,
    real.sqr: lambda x: x**2,
    real.exp: flint.arb.exp,
    real.ln: flint.arb.log,
    real.sin: flint.arb.sin,
    real.cos: flint.arb.cos,
    real.tan: flint.arb.tan,
    real.atan: flint.arb.atan,
    real.pow: lambda x, y: x**y,
    real.pi.decl(): flint.arb.pi,
    (a + b).decl(): op.add,
    (a * b).decl(): op.mul,
    (a / b).decl(): op.truediv,
    (a - b).decl(): op.sub,
    (a**b).decl(): op.pow,
}


def interp_flint(e, env):
    if e in env:
        return env[e]
    elif smt.is_select(e) and e.arg(0) in flint_decls:
        return flint_decls[e.arg(0)](
            *[interp_flint(arg, env) for arg in e.children()[1:]]
        )
    elif smt.is_app(e) and e.decl() in flint_decls:
        decl = e.decl()
        return flint_decls[decl](*[interp_flint(arg, env) for arg in e.children()])
    assert False, f"Can't interpret {e} into flint"


def z3_of_arb(x: flint.arb) -> tuple[smt.ArithRef, smt.ArithRef]:
    if not x.is_finite():
        raise ValueError("Infinite value in z3_of_arb", x)
    mid = x.mid().str(100, more=True, radius=True)
    rad = x.rad().str(100, more=True, radius=True)
    # +/- does not appear if matches arb exactly
    if "+/-" in mid or "+/-" in rad:
        raise ValueError("Unexpected error in conversion from arb to z3", mid, rad)
    return smt.RealVal(mid), smt.RealVal(rad)


def flint_bnd(t: smt.ExprRef, env):
    assert smt.is_real(t)
    assert all(smt.is_real(k) and isinstance(v, flint.arb) for k, v in env.items())
    preconds = [smt.BoolVal(True)]
    for k, v in env.items():
        mid, rad = z3_of_arb(v)
        preconds.append(mid - rad <= k)
        preconds.append(k <= mid + rad)
    v = interp_flint(t, env)
    if not v.is_finite():
        raise ValueError("Infinite value in flint_bnd", t, env, v)
    mid, rad = z3_of_arb(v)
    if len(env) > 0:
        return kd.axiom(
            kd.QForAll(
                list(env.keys()), smt.And(preconds), mid - rad <= t, t <= mid + rad
            ),
            by="flint_eval",
        )
    else:
        return kd.axiom(smt.And(mid - rad <= t, t <= mid + rad), by="flint_eval")


a, b = smt.Reals("a b")
sympy_decls = {
    real.sqrt: sympy.sqrt,
    real.sqr: lambda x: x**2,
    real.exp: sympy.exp,
    real.ln: sympy.ln,
    real.sin: sympy.sin,
    real.cos: sympy.cos,
    real.tan: sympy.tan,
    real.atan: sympy.atan,
    real.pow: op.pow,
    (a + b).decl(): sympy.Add,
    (a * b).decl(): sympy.Mul,
    (a / b).decl(): op.truediv,
    (a - b).decl(): op.sub,
    (a**b).decl(): sympy.Pow,
    (a == b).decl(): sympy.Eq,
}
rev_sympy_decls = {v: k for k, v in sympy_decls.items()}


def interp_sympy(e: smt.ExprRef, env: dict[smt.ExprRef, sympy.Expr]) -> sympy.Expr:
    if e in env:
        return env[e]
    elif smt.is_app(e) and e.decl() in sympy_decls:
        decl = e.decl()
        return sympy_decls[decl](*[interp_sympy(arg, env) for arg in e.children()])
    assert False, f"Can't interpret {e} into sympy"


def sympyify(e: smt.ExprRef) -> sympy.Expr:
    return interp_sympy(e, {})


"""
def z3_of_sympy(x: sympy.Expr, env: dict[sympy.Expr, smt.ExprRef]) -> smt.ExprRef:
    decl = rev_sympy_decls.get(x.func)
    if x in env:
        return env[x]
    elif decl is not None:
        return decl(*[z3_of_sympy(arg) for arg in x.args])
    else:
        raise ValueError("Can't interpret", x, "from sympy into z3")


def factor(vs, e: smt.ExprRef):
    env1 = {e: sympy.symbols(e.name()) for e in vs}
    env2 = {v: k for k, v in env1.items()}
    return sympy.interp_sympy(e, env1).factor()
"""
