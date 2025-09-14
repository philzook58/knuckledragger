import kdrag.smt as smt
import subprocess
import kdrag.solvers as solvers
# import kdrag.theories.real as real


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
