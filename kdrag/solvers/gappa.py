import kdrag.smt as smt
import kdrag as kd
import subprocess
import kdrag.solvers as solvers
import kdrag.theories.real as real
import sympy
import flint
import operator as op

"""
WIP

Gappa is a solver for rigorous bounds on real arithmetic expressions.
It includes rigorous models of floating point rounding.
https://gappa.gitlabpages.inria.fr/gappa/language.html

TODO:
define rounding operations in theories.real. Special printing for them. Possibly a prelude.
Nesting of logical operations may not be doing what I expect?
"""


def gappa_of_bool(e: smt.BoolRef):
    assert isinstance(e, smt.BoolRef)
    if smt.is_and(e):
        return "(" + " /\\ ".join(map(gappa_of_bool, e.children())) + ")"
    elif smt.is_or(e):
        return "(" + "\\/ ".join(map(gappa_of_bool, e.children())) + ")"
    elif smt.is_not(e):
        return f"(not {gappa_of_bool(e.arg(0))})"
    elif smt.is_implies(e):
        hyp, conc = map(gappa_of_bool, e.children())
        return f"({hyp} -> {conc})"
    elif smt.is_app(e):
        decl = e.decl()
        dname = decl.name()
        nargs = decl.arity()
        children = map(gappa_of_real, e.children())
        if dname == "<=" or dname == "<" or dname == ">=" or dname == ">":
            lhs, rhs = children
            # rhs of gappa ineq has to be a constant.
            # We get stronger inferences if we use that form
            if isinstance(e.arg(1), smt.RatNumRef):
                return f"({lhs} {dname} {rhs})"
            else:
                return f"({lhs} - {rhs} {dname} 0)"
        elif dname == "=":
            lhs, rhs = children
            return f"({lhs} = {rhs})"
        else:
            raise ValueError("Unsupported expression for Gappa: " + str(e))
    elif smt.is_quantifier(e):
        raise ValueError("Gappa does not support quantifiers: " + str(e))
    else:
        raise ValueError("Unsupported expression for Gappa: " + str(e))


def gappa_of_real(e: smt.ArithRef):
    assert smt.is_real(e)
    if isinstance(e, smt.RatNumRef):
        v = e.as_decimal(10)
        if "?" in v:
            raise ValueError("Gappa only supports finite decimal constants: " + str(e))
        return v
    elif smt.is_app(e):
        decl = e.decl()
        dname = decl.name()
        nargs = decl.arity()
        children = map(gappa_of_real, e.children())
        if dname == "+":  # could refactor + and * into same case.
            return "(" + " + ".join(children) + ")"
        elif dname == "-" and e.decl().num_:  # is_sub
            x, y = children
            return f"({x} - {y})"
        elif dname == "*":
            return "(" + " * ".join(children) + ")"
        elif dname == "/":
            x, y = children
            return f"({x} / {y})"
        # elif dname == "sqrt":
        #    return f"sqrt({gappa_of_expr(e.get_arg(0))})"
        elif dname == "abs":
            return f"|{children[0]}|"
        # elif dname == "fma":
        #    x,y,z = map(gappa_of_expr, e.children())
        #    return f"fma({x},{y},{z})"
        else:
            if nargs == 0:
                return dname
            else:  # should I allow this?
                return f"{dname}({','.join(map(gappa_of_real,e.children()))})"
    else:
        raise ValueError("Unsupported expression for Gappa: " + str(e))


class GappaSolver(solvers.BaseSolver):
    def check(self):
        with open("/tmp/gappa.g", "w") as fp:
            fp.write("{" + gappa_of_bool(smt.And(self.adds)) + "}")
            fp.flush()
        self.res = subprocess.run(
            [solvers.binpath("gappa/src/gappa"), "/tmp/gappa.g"], capture_output=True
        )
        return self.res

    def bound(self, e: smt.ExprRef):
        with open("/tmp/gappa.g", "w") as fp:
            fp.write(
                f"{{ {gappa_of_bool(smt.And(self.adds))} -> {gappa_of_real(e)} in ?}}"
            )
            fp.flush()
        self.res = subprocess.run(
            [solvers.binpath("gappa/src/gappa"), "/tmp/gappa.g"], capture_output=True
        )
        return self.res


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
    (a + b).decl(): op.add,
    (a * b).decl(): op.mul,
    (a / b).decl(): op.truediv,
    (a - b).decl(): op.sub,
    (a**b).decl(): sympy.Pow,
    (a == b).decl(): sympy.Eq,
}


def interp_sympy(e: smt.ExprRef, env: dict[smt.ExprRef, sympy.Expr]) -> sympy.Expr:
    if e in env:
        return env[e]
    elif smt.is_app(e) and e.decl() in sympy_decls:
        decl = e.decl()
        return sympy_decls[decl](*[interp_sympy(arg, env) for arg in e.children()])
    assert False, f"Can't interpret {e} into sympy"


def sympyify(e: smt.ExprRef) -> sympy.Expr:
    return interp_sympy(e, {})
