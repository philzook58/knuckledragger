"""
In some cases, the default smtlib printers in z3 do not output reparseable SMT-LIB code for other solvers.
Z3 has some extra features, and also identical names with different sorts may need to be mangled
This module provides SMT-LIB printers for such cases.
"""

import kdrag.smt as smt
import kdrag as kd

# Some are polymorphic so decl doesn't work
# predefined theory symbols don't need function declarations
predefined_names = [
    "=",
    "if",
    "and",
    "or",
    "not",
    "=>",
    "select",
    "store",
    "=>",
    ">",
    "<",
    ">=",
    "<=",
    "+",
    "-",
    "*",
    "/",
    # "^",
    "is",
    "Int",
    "Real",
    "abs",
    "distinct",
    "true",
    "false",
    "bvor",
    "bvand",
    "bvxor",
    "bvnot",
    "bvadd",
    "bvsub",
    "bvmul",
    "bvudiv",
    "bvurem",
    "bvshl",
    "bvlshr",
    "bvashr",
    "bvult",
    "bvule",
    "bvugt",
    "bvuge",
]


def mangle_decl_smtlib(d: smt.FuncDeclRef):
    """Mangle a declaration to remove overloading"""
    id_, name = d.get_id(), d.name()
    assert id_ >= 0x80000000
    return name + "_" + format(id_ - 0x80000000, "x")


def expr_to_smtlib(expr: smt.ExprRef):
    if isinstance(expr, smt.QuantifierRef):
        quantifier = (
            "forall" if expr.is_forall() else "exists" if expr.is_exists() else "lambda"
        )
        vs, body = kd.utils.open_binder(expr)
        vs = " ".join(
            [f"({mangle_decl_smtlib(v.decl())} {v.sort().sexpr()})" for v in vs]
        )
        # vs = " ".join(
        #    [f"({expr.var_name(i)} {expr.var_sort(i)})" for i in range(expr.num_vars())]
        # )

        return f"({quantifier} ({vs}) {expr_to_smtlib(body)})"
    elif kd.utils.is_value(expr):
        return expr.sexpr()
    elif smt.is_const(expr):
        decl = expr.decl()
        name = decl.name()
        if name in predefined_names:
            if name == "and":  # 0-arity applications
                return "true"
            elif name == "or":
                return "false"
            else:
                return expr.decl().name()
        return mangle_decl_smtlib(expr.decl())
    elif smt.is_app(expr):
        decl = expr.decl()
        name = decl.name()
        children = " ".join([expr_to_smtlib(c) for c in expr.children()])
        if name in predefined_names:
            if name == "if":
                name = "ite"
            elif name == "is":
                dt = decl.domain(0)
                assert isinstance(dt, smt.DatatypeSortRef)
                # find out which
                for i in range(dt.num_constructors()):
                    if decl == dt.recognizer(i):
                        name = f"(_ is {mangle_decl_smtlib(dt.constructor(i))})"
                        break
            return f"({name} {children})"
        else:
            return f"({mangle_decl_smtlib(decl)} {children})"
    elif smt.is_var(expr):
        assert False
    else:
        return expr.sexpr()


def funcdecl_smtlib(decl: smt.FuncDeclRef):
    dom = " ".join([(decl.domain(i).sexpr()) for i in range(decl.arity())])
    return f"(declare-fun {mangle_decl_smtlib(decl)} ({dom}) {decl.range().sexpr()})"


# TODO. We need to mangle the declarations
def smtlib_datatypes(dts: list[smt.DatatypeSortRef]) -> str:
    res = []
    for dt in dts:
        res.append(f"(declare-datatypes (({dt.name()} 0)) ((")
        for i in range(dt.num_constructors()):
            c = dt.constructor(i)
            res.append(f" ({mangle_decl_smtlib(c)}")
            for j in range(c.arity()):
                acc = dt.accessor(i, j)
                res.append(f" ({mangle_decl_smtlib(acc)} {acc.range()})")
            res.append(")")
        res.append(")))\n")
    return "".join(res)
