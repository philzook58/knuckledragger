from kdrag.kernel import is_proof
import kdrag.smt as smt
import subprocess
import sys
import kdrag as kd
from typing import Optional


def simp(t: smt.ExprRef) -> smt.ExprRef:
    expr = smt.FreshConst(t.sort(), prefix="knuckle_goal")
    G = smt.Goal()
    for v in kd.kernel.defns.values():
        G.add(v.ax.thm)
    G.add(expr == t)
    G2 = smt.Then(smt.Tactic("demodulator"), smt.Tactic("simplify")).apply(G)[0]
    # TODO make this extraction more robust
    return G2[len(G2) - 1].children()[1]


def simp2(t: smt.ExprRef) -> smt.ExprRef:
    expr = smt.FreshConst(t.sort(), prefix="knuckle_goal")
    G = smt.Goal()
    for v in kd.kernel.defns.values():
        G.add(v.ax.thm)
    G.add(expr == t)
    G2 = smt.Tactic("elim-predicates").apply(G)[0]
    return G2[len(G2) - 1].children()[1]


def lemma_smt(thm: smt.BoolRef, by=[], sig=[]) -> list[str]:
    """
    Replacement for lemma that returns smtlib string for experimentation with other solvers
    """
    output = []
    output.append(";;declarations")
    for f in sig:
        if isinstance(f, smt.FuncDeclRef):
            output.append(f.sexpr())
        elif isinstance(f, smt.SortRef):
            output.append("(declare-sort " + f.sexpr() + " 0)")
        elif isinstance(f, smt.ExprRef):
            output.append(f.decl().sexpr())
    output.append(";;axioms")
    for e in by:
        if is_proof(e):
            output.append("(assert " + e.thm.sexpr() + ")")
    output.append(";;goal")
    output.append("(assert " + smt.Not(thm).sexpr() + ")")
    output.append("(check-sat)")
    return output


def z3_match(
    t: smt.ExprRef, pat: smt.ExprRef
) -> Optional[dict[smt.ExprRef, smt.ExprRef]]:
    """
    Pattern match t against pat. Variables are constructed as `smt.Var(i, sort)`.
    Returns substitution dict if match succeeds.
    Returns None if match fails.
    Outer quantifier (Exists, ForAll, Lambda) in pat is ignored.
    """
    if smt.is_quantifier(pat):
        pat = pat.body()
    subst = {}
    todo = [(t, pat)]
    while len(todo) > 0:
        t, pat = todo.pop()
        if t.eq(pat):
            continue
        if smt.is_var(pat):
            if pat in subst:
                if not subst[pat].eq(t):
                    return None
            else:
                subst[pat] = t
        elif smt.is_app(t) and smt.is_app(pat):
            if pat.decl() == t.decl():
                todo.extend(zip(t.children(), pat.children()))
            else:
                return None
        else:
            raise Exception("Unexpected subterm or subpattern", t, pat)
    return subst


def open_binder(lam: smt.QuantifierRef):
    vars = [
        smt.Const(lam.var_name(i).upper(), lam.var_sort(i))
        for i in reversed(range(lam.num_vars()))
    ]
    return vars, smt.substitute_vars(lam.body(), *vars)


def mangle_decl(d: smt.FuncDeclRef):
    return d.name() + "_" + format(d.get_id() - 0x80000000, "x")


def expr_to_tptp(expr: smt.ExprRef, thf=True):
    if isinstance(expr, smt.IntNumRef):
        return str(expr.as_string())
    elif isinstance(expr, smt.QuantifierRef):
        vars, body = open_binder(expr)
        body = expr_to_tptp(body)
        vs = ", ".join(
            [mangle_decl(v.decl()) + ":" + sort_to_tptp(v.sort()) for v in vars]
        )
        if expr.is_forall():
            return f"(![{vs}] : {body})"
        elif expr.is_exists():
            return f"(?[{vs}] : {body})"
        elif expr.is_lambda():
            if not thf:
                raise Exception(
                    "Lambda not supported in tff tptp format. Try a thf solver", expr
                )
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
    elif head == "if":
        # if thf:
        #    return "($ite @ {} @ {} @ {})".format(*children)
        # else:
        return "$ite({}, {}, {})".format(*children)
    elif head == "select":
        return "({} @ {})".format(*children)
    elif head == "distinct":
        if len(children) == 2:
            return "({} != {})".format(*children)
        return "$distinct({})".format(", ".join(children))
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
        if len(children) == 1:
            return "$difference(0,{})".format(children[0])
        else:
            return "$difference({},{})".format(*children)
    elif head == "*":
        return "$product({},{})".format(*children)
    elif head == "/":
        return "$quotient({},{})".format(*children)
    elif head == "^":
        return "$power({},{})".format(
            *children
        )  # This is not a built in tptp function though
    else:
        head = mangle_decl(expr.decl())
        if len(children) == 0:
            return head
        if thf:
            return f"({head} @ {' @ '.join(children)})"
        else:
            return f"{head}({', '.join(children)})"


smt.ExprRef.tptp = expr_to_tptp


def sort_to_tptp(sort: smt.SortRef):
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


smt.SortRef.tptp = sort_to_tptp


def lemma_tptp(thm: smt.BoolRef, by=[], sig=[], timeout=None, command=None):
    """
    Returns tptp strings
    """
    output = []
    for f in sig:
        if isinstance(f, smt.FuncDeclRef):
            dom = " * ".join([f.domain(i).tptp() for i in range(f.arity())])
            output.append(f"tff(sig, type, {f.name()} : ({dom}) > {f.range().tptp()}).")
        elif isinstance(f, smt.SortRef):
            output.append(f"tff(sig, type, {f.tptp()} : $tType).")
        elif isinstance(f, smt.ExprRef):
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


def subterms(t: smt.ExprRef):
    todo = [t]
    while len(todo) > 0:
        x = todo.pop()
        yield x
        todo.extend(x.children())


def sorts(t: smt.ExprRef):
    for t in subterms(t):
        yield t.sort()


def decls(t: smt.ExprRef):
    for t in subterms(t):
        if smt.is_app(t):
            yield t.decl()


def lemma_db():
    """Scan all modules for Proof objects and return a dictionary of them."""
    db = {}
    for modname, mod in sys.modules.items():
        thms = {name: thm for name, thm in mod.__dict__.items() if is_proof(thm)}
        if len(thms) > 0:
            db[modname] = thms
    return db


def induct(DT: smt.DatatypeSortRef):
    """Build a basic induction principle for an algebraic datatype"""
    P = smt.FreshConst(smt.ArraySort(DT, smt.BoolSort()), prefix="P")
    hyps = []
    for i in range(DT.num_constructors()):
        constructor = DT.constructor(i)
        args = [
            smt.FreshConst(constructor.domain(j), prefix="a")
            for j in range(constructor.arity())
        ]
        acc = P[constructor(*args)]
        for arg in args:
            if arg.sort() == DT:
                acc = kd.QForAll([arg], P[arg], acc)
            else:
                acc = kd.QForAll([arg], acc)
        hyps.append(acc)
    x = smt.FreshConst(DT, prefix="x")
    conc = kd.QForAll([x], P[x])
    return smt.Implies(smt.And(hyps), conc)
