from knuckledragger.kernel import lemma, is_proof
import z3
import subprocess
import sys
import knuckledragger as kd
from typing import Optional


def simp(t: z3.ExprRef) -> z3.ExprRef:
    expr = z3.FreshConst(t.sort(), prefix="knuckle_goal")
    G = z3.Goal()
    for v in kd.kernel.defns.values():
        G.add(v.ax.thm)
    G.add(expr == t)
    G2 = z3.Then(z3.Tactic("demodulator"), z3.Tactic("simplify")).apply(G)[0]
    # TODO make this extraction more robust
    return G2[len(G2) - 1].children()[1]


def simp2(t: z3.ExprRef) -> z3.ExprRef:
    expr = z3.FreshConst(t.sort(), prefix="knuckle_goal")
    G = z3.Goal()
    for v in kd.kernel.defns.values():
        G.add(v.ax.thm)
    G.add(expr == t)
    G2 = z3.Tactic("elim-predicates").apply(G)[0]
    return G2[len(G2) - 1].children()[1]


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


def z3_match(t: z3.ExprRef, pat: z3.ExprRef) -> Optional[dict[z3.ExprRef, z3.ExprRef]]:
    """
    Pattern match t against pat. Variables are constructed as `z3.Var(i, sort)`.
    Returns substitution dict if match succeeds.
    Returns None if match fails.
    Outer quantifier (Exists, ForAll, Lambda) in pat is ignored.
    """
    if z3.is_quantifier(pat):
        pat = pat.body()
    subst = {}
    todo = [(t, pat)]
    while len(todo) > 0:
        t, pat = todo.pop()
        if t.eq(pat):
            continue
        if z3.is_var(pat):
            if pat in subst:
                if not subst[pat].eq(t):
                    return None
            else:
                subst[pat] = t
        elif z3.is_app(t) and z3.is_app(pat):
            if pat.decl() == t.decl():
                todo.extend(zip(t.children(), pat.children()))
            else:
                return None
        else:
            raise Exception("Unexpected subterm or subpattern", t, pat)
    return subst


def open_binder(lam: z3.QuantifierRef):
    vars = [
        z3.Const(lam.var_name(i).upper(), lam.var_sort(i))
        for i in reversed(range(lam.num_vars()))
    ]
    return vars, z3.substitute_vars(lam.body(), *vars)


def expr_to_tptp(expr: z3.ExprRef):
    if isinstance(expr, z3.IntNumRef):
        return str(expr.as_string())
    elif isinstance(expr, z3.QuantifierRef):
        vars, body = open_binder(expr)
        body = expr_to_tptp(body)
        vs = ", ".join([v.sexpr() + ":" + sort_to_tptp(v.sort()) for v in vars])
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


def sort_to_tptp(sort: z3.SortRef):
    name = sort.name()
    if name == "Int":
        return "$int"
    elif name == "Bool":
        return "$o"
    elif name == "Real":
        return "$real"
    elif name == "Array":
        return "({} > {})".format(
            sort_to_tptp(sort.domain()), sort_to_tptp(sort.range())
        )
    else:
        return name.lower()


z3.SortRef.tptp = sort_to_tptp


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
    if command is None:
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


def subterms(t: z3.ExprRef):
    todo = [t]
    while len(todo) > 0:
        x = todo.pop()
        yield x
        todo.extend(x.children())


def lemma_db():
    """Scan all modules for Proof objects and return a dictionary of them."""
    db = {}
    for modname, mod in sys.modules.items():
        thms = {name: thm for name, thm in mod.__dict__.items() if is_proof(thm)}
        if len(thms) > 0:
            db[modname] = thms
    return db
