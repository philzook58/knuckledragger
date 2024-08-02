from knuckledragger.kernel import lemma, is_proof
import z3
import subprocess
import sys


class Calc:
    """
    calc is for equational reasoning.
    One can write a sequence of formulas interspersed with useful lemmas.
    """

    def __init__(self, vars, lhs):
        # TODO: hyps=None for conditional rewriting. assumpt, assume=[]
        self.vars = vars
        self.terms = [lhs]
        self.lemmas = []

    def ForAll(self, body):
        if len(self.vars) == 0:
            return body
        else:
            return z3.ForAll(self.vars, body)

    def eq(self, rhs, by=[]):
        self.lemmas.append(lemma(self.ForAll(self.terms[-1] == rhs), by=by))
        self.terms.append(rhs)
        return self

    # TODO: lt, le, gt, ge chaining. Or custom op.

    def __repr__(self):
        return "... = " + repr(self.terms[-1])

    def qed(self):
        return lemma(self.ForAll(self.terms[0] == self.terms[-1]), by=self.lemmas)


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
    name = sort.name()
    if name == "Int":
        return "$int"
    elif name == "Bool":
        return "$o"
    elif name == "Real":
        return "$real"
    elif name == "Array":
        return "({} > {})".format(
            z3_sort_tptp(sort.domain()), z3_sort_tptp(sort.range())
        )
    else:
        return name.lower()


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


def lemma_db():
    """Scan all modules for Proof objects and return a dictionary of them."""
    db = {}
    for modname, mod in sys.modules.items():
        thms = {name: thm for name, thm in mod.__dict__.items() if is_proof(thm)}
        if len(thms) > 0:
            db[modname] = thms
    return db
