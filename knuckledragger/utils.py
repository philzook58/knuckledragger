from numpy import isin
from knuckledragger.kernel import lemma, is_proof
import z3
from operator import eq
import subprocess


def calc(*args, vars=None, by=[], op=eq):
    """
    calc is for equational reasoning.
    One can write a sequence of formulas interspersed with useful lemmas.
    Inequational chaining can be done via op=lambda x,y: x <= y
    """

    def thm(lhs, rhs):
        if vars == None:
            return op(lhs, rhs)
        else:
            return z3.ForAll(vars, op(lhs, rhs))

    lemmas = []
    local_by = []
    lhs = args[0]
    for arg in args[1:]:
        if is_proof(arg):
            local_by.append(arg)
        else:
            lemmas.append(lemma(thm(lhs, arg), by=by + local_by))
            lhs = arg
            local_by = []
    return lemma(thm(args[0], args[-1]), by=by + lemmas)


def lemma_smt(thm: z3.BoolRef, by=[], sig=[]) -> list[str]:
    """
    Replacement for lemma that returns smtlib string for experimentation with other solvers
    """
    output = []
    output.append(";;declarations")
    for f in sig:
        if isinstance(f, z3.FuncDeclRef):
            output.append(f.sexpr())
        elif isinstance(f, z3.SortRef):
            output.append("(declare-sort " + f.sexpr() + " 0)")
        elif isinstance(f, z3.ExprRef):
            output.append(f.decl().sexpr())
    output.append(";;axioms")
    for e in by:
        if is_proof(e):
            output.append("(assert " + e.thm.sexpr() + ")")
    output.append(";;goal")
    output.append("(assert " + z3.Not(thm).sexpr() + ")")
    output.append("(check-sat)")
    return output


def open_binder(l: z3.QuantifierRef):
    vars = [
        z3.Const(l.var_name(i).upper(), l.var_sort(i))
        for i in reversed(range(l.num_vars()))
    ]
    return vars, z3.substitute_vars(l.body(), *vars)


def expr_to_tptp(expr: z3.ExprRef):
    if isinstance(expr, z3.IntNumRef):
        return str(expr.as_string())
    elif isinstance(expr, z3.QuantifierRef):
        vars, body = open_binder(expr)
        body = expr_to_tptp(body)
        vs = ", ".join([v.sexpr() + ":" + z3_sort_tptp(v.sort()) for v in vars])
        if expr.is_forall():
            return f"(![{vs}] : {body})"
        elif expr.is_exists():
            return f"(?[{vs}] : {body})"
        elif expr.is_lambda():
            return f"(^[{vs}] : {body})"
    children = list(map(expr_to_tptp, expr.children()))
    head = expr.decl().name()
    if head == "true":
        return "$true"
    elif head == "false":
        return "$false"
    elif head == "and":
        return "({})".format(" & ".join(children))
    elif head == "or":
        return "({})".format(" | ".join(children))
    elif head == "=":
        return "({} = {})".format(children[0], children[1])
    elif head == "=>":
        return "({} => {})".format(children[0], children[1])
    elif head == "not":
        return "~({})".format(children[0])
    elif head == "ite":
        return "$ite({}, {}, {})".format(*children)
    elif head == "<":
        return "$less({},{})".format(*children)
    elif head == "<=":
        return "$lesseq({},{})".format(*children)
    elif head == ">":
        return "$greater({},{})".format(*children)
    elif head == ">=":
        return "$greatereq({},{})".format(*children)
    elif head == "+":
        return "$sum({},{})".format(*children)
    elif head == "-":
        return "$difference({},{})".format(*children)
    elif head == "*":
        return "$product({},{})".format(*children)
    elif head == "/":
        return "$quotient({},{})".format(*children)
    else:
        if len(children) == 0:
            return head
        return f"{head}({', '.join(children)})"


z3.ExprRef.tptp = expr_to_tptp


def z3_sort_tptp(sort: z3.SortRef):
    match sort.name():
        case "Int":
            return "$int"
        case "Bool":
            return "$o"
        case "Real":
            return "$real"
        case "Array":
            return "({} > {})".format(
                z3_sort_tptp(sort.domain()), z3_sort_tptp(sort.range())
            )
        case x:
            return x.lower()


z3.SortRef.tptp = z3_sort_tptp


def lemma_tptp(thm: z3.BoolRef, by=[], sig=[], timeout=None, command=None):
    """
    Returns tptp strings
    """
    output = []
    for f in sig:
        if isinstance(f, z3.FuncDeclRef):
            dom = " * ".join([f.domain(i).tptp() for i in range(f.arity())])
            output.append(f"tff(sig, type, {f.name()} : ({dom}) > {f.range().tptp()}).")
        elif isinstance(f, z3.SortRef):
            output.append(f"tff(sig, type, {f.tptp()} : $tType).")
        elif isinstance(f, z3.ExprRef):
            output.append(f"tff(sig, type, {f.sexpr()} : {f.sort().tptp()}).")
    for e in by:
        if is_proof(e):
            output.append(f"tff(hyp, axiom, {e.thm.tptp()} ).")
    output.append(f"tff(goal,conjecture,{thm.tptp()} ).")
    if command == None:
        return output
    else:
        with open("/tmp/temp.p", "w") as f:
            f.writelines(output)
        command.append("/tmp/temp.p")
        res = subprocess.run(
            command,
            timeout=timeout,
            capture_output=True,
        )
        return res
