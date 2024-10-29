from kdrag.kernel import is_proof
import kdrag.smt as smt
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


def pmatch(
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
    # Open with capitalized names to match tptp conventions
    vars = [
        smt.Const(lam.var_name(i).upper(), lam.var_sort(i))
        for i in reversed(range(lam.num_vars()))
    ]
    return vars, smt.substitute_vars(lam.body(), *vars)


def occurs(x, t):
    if smt.is_var(t):
        return x.eq(t)
    if smt.is_app(t):
        return any(occurs(x, t.arg(i)) for i in range(t.num_args()))
    return False


def unify(p1, p2):
    subst = {}
    todo = [(p1, p2)]
    while todo:
        p1, p2 = todo.pop()  # we could pop _any_ of the todos, not just the top.
        if p1.eq(p2):  # delete
            continue
        elif smt.is_var(p1):  # elim
            if occurs(p1, p2):
                return None
            todo = [
                (smt.substitute(t1, (p1, p2)), smt.substitute(t2, (p1, p2)))
                for (t1, t2) in todo
            ]
            subst = {k: smt.substitute(v, (p1, p2)) for k, v in subst.items()}
            subst[p1] = p2
        elif smt.is_var(p2):  # orient
            todo.append((p2, p1))
        elif smt.is_app(p1):  # decompose
            if not smt.is_app(p2) or p1.decl() != p2.decl():
                return None
            todo.extend(zip(p1.children(), p2.children()))
        else:
            raise Exception("unexpected case", p1, p2)
    return subst


"""
def apply_horn(thm: smt.BoolRef, horn: smt.BoolRef) -> smt.BoolRef:
    pat = horn
    obl = []
    if smt.is_quantifier(pat) and pat.is_forall():
        pat = pat.body()
    while True:
        if smt.is_implies(pat):
            obl.append(pat.arg(0))
            pat = pat.arg(1)
        else:
            break
    return kd.utils.z3_match(thm, pat)


def horn_split(horn: smt.BoolRef) -> smt.BoolRef:
    body = []
    vs = []
    while True:
        if smt.is_quantifier(horn) and horn.is_forall():
            vs1, horn = open_binder(horn)
            vs.extend(vs1)
        if smt.is_implies(horn):
            body.append(horn.arg(0))
            horn = horn.arg(1)
        else:
            break
    head = horn
    return vs, body, head
"""


def generate(sort: smt.SortRef):
    """A generator of values for a sort"""
    s = smt.Solver()
    x, y = smt.Consts("x y", sort)
    s.add(x == y)  # trick to actually have x in model
    if sort in kd.notation.wf.methods:
        s.add(kd.notation.wf(x))
    while s.check() == smt.sat:
        m = s.model()
        yield m.eval(x)
        s.add(x != m.eval(x))


def mangle_decl(d: smt.FuncDeclRef, env=[]):
    # single quoted (for operators) + underscore + hex id
    id_, name = d.get_id(), d.name()
    assert id_ >= 0x80000000
    if d in env:
        return d.name() + "_" + format(id_ - 0x80000000, "x")
    else:
        return d.name() + "_" + format(id_ - 0x80000000, "x")
        # TODO: single quote is not working.
        # return "'" + d.name() + "_" + format(id_ - 0x80000000, "x") + "'"


def expr_to_tptp(expr: smt.ExprRef, env=None, format="thf", theories=True):
    if env is None:
        env = []
    if isinstance(expr, smt.IntNumRef):
        return str(expr.as_string())
    elif isinstance(expr, smt.QuantifierRef):
        vars, body = open_binder(expr)
        env = env + [v.decl() for v in vars]
        body = expr_to_tptp(body, env=env, format=format, theories=theories)
        if format == "fof":
            vs = ", ".join([mangle_decl(v.decl(), env) for v in vars])
            type_preds = " & ".join(
                [
                    f"{sort_to_tptp(v.sort())}({mangle_decl(v.decl(), env)}))"
                    for v in vars
                ]
            )
        else:
            vs = ", ".join(
                [
                    mangle_decl(v.decl(), env) + ":" + sort_to_tptp(v.sort())
                    for v in vars
                ]
            )
        if expr.is_forall():
            if format == "fof":
                # TODO: is adding type predicates necessary?
                # return f"(![{vs}] : ({type_preds}) => {body})"
                return f"(![{vs}] : {body})"
            return f"(![{vs}] : {body})"
        elif expr.is_exists():
            if format == "fof":
                # return f"(?[{vs}] : ({type_preds}) & {body})"
                return f"(?[{vs}] : {body})"
            return f"(?[{vs}] : {body})"
        elif expr.is_lambda():
            if format != "thf":
                raise Exception(
                    "Lambda not supported in tff tptp format. Try a thf solver", expr
                )
            return f"(^[{vs}] : {body})"
    assert smt.is_app(expr)
    children = [
        expr_to_tptp(c, env=env, format=format, theories=theories)
        for c in expr.children()
    ]
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
        assert format == "thf"
        return "({} @ {})".format(*children)
    elif head == "distinct":
        if len(children) == 2:
            return "({} != {})".format(*children)
        return "$distinct({})".format(", ".join(children))

    if theories:
        if head == "<":
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
        # elif head == "^":
        #    return "$power({},{})".format(
        #        *children
        #    )  # This is not a built in tptp function though
    # default assume regular term
    head = mangle_decl(expr.decl(), env)
    if len(children) == 0:
        return head
    if format == "thf":
        return f"({head} @ {' @ '.join(children)})"
    else:
        return f"{head}({', '.join(children)})"


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


def expr_to_lean(expr: smt.ExprRef):
    # TODO
    pass


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


import os
import glob
import inspect


def prompt(prompt: str):
    """
    Get the root directory of the current package, find all .py files within
    that directory, and concatenate their contents into a single string separated by `---`.

    Returns:
        str: A single string with all .py files concatenated, separated by `---`.
    """
    excluded_subdirs = ["eprover"]
    current_file = inspect.getfile(inspect.currentframe())
    root_dir = os.path.dirname(os.path.abspath(current_file))

    py_files = glob.glob(
        os.path.join(root_dir, "theories", "**", "*.py"), recursive=True
    )

    combined_content = [
        """
    The following is the code of the python project Knuckledragger.
    It is a semiautomated theorem prover that uses z3py and other solvers to disharge obligations.
    The syntax tree is literally z3.
    The Proof datatype is a protected wrapped z3 BoolRef object.
    Proofs largely proceed by stating small steps with reference to previously proofs in the `by` parameter of `lemma` 
    \n\n\n
    """
    ]
    for file_path in py_files:
        if any(
            excluded in os.path.relpath(file_path, root_dir).split(os.sep)
            for excluded in excluded_subdirs
        ):
            continue
        with open(file_path, "r", encoding="utf-8") as file:
            combined_content += "\n\n\n---" + file_path + "\n\n\n"
            combined_content += file.read()
    combined_content += "\n\n\n" + prompt + "\n\n\n"

    return "".join(combined_content)
