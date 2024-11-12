from kdrag.kernel import is_proof
import kdrag.smt as smt
import sys
import kdrag as kd
from typing import Optional, NamedTuple


def simp(t: smt.ExprRef) -> smt.ExprRef:
    """simplify a term using z3 built in simplifier"""
    expr = smt.FreshConst(t.sort(), prefix="knuckle_goal")
    G = smt.Goal()
    for v in kd.kernel.defns.values():
        G.add(v.ax.thm)
    G.add(expr == t)
    G2 = smt.Then(smt.Tactic("demodulator"), smt.Tactic("simplify")).apply(G)[0]
    # TODO make this extraction more robust
    return G2[len(G2) - 1].children()[1]


def simp2(t: smt.ExprRef) -> smt.ExprRef:
    """simplify a term using z3 built in simplifier"""
    expr = smt.FreshConst(t.sort(), prefix="knuckle_goal")
    G = smt.Goal()
    for v in kd.kernel.defns.values():
        G.add(v.ax.thm)
    G.add(expr == t)
    G2 = smt.Tactic("elim-predicates").apply(G)[0]
    return G2[len(G2) - 1].children()[1]


# TODO: Doesn't seem to do anything?
# def factor(t: smt.ExprRef) -> smt.ExprRef:
#    """factor a term using z3 built in tactic"""
#    expr = smt.FreshConst(t.sort(), prefix="knuckle_goal")
#    G = smt.Goal()
#    for v in kd.kernel.defns.values():
#        G.add(v.ax.thm)
#    G.add(expr == t)
#    G2 = smt.Tactic("factor").apply(G)[0]
#    return G2[len(G2) - 1].children()[1]


def pmatch_db(
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


def pmatch(
    t: smt.ExprRef, vs: list[smt.ExprRef], pat: smt.ExprRef
) -> Optional[dict[smt.ExprRef, smt.ExprRef]]:
    """Pattern match t against pat considering vs as variables. Returns substitution dictionary if succeeds"""
    subst = {}
    todo = [(t, pat)]
    while len(todo) > 0:
        t, pat = todo.pop()
        if t.eq(pat):
            continue
        if any(pat.eq(v) for v in vs):
            if pat in subst:
                if not subst[pat].eq(t):
                    return None
            else:
                subst[pat] = t
        elif smt.is_app(pat):
            if smt.is_app(t) and pat.decl() == t.decl():
                todo.extend(zip(t.children(), pat.children()))
            else:
                return None
        else:
            raise Exception("Unexpected subterm or subpattern in pmatch", t, pat)
    return subst


def rewrite1(
    t: smt.ExprRef, vs: list[smt.ExprRef], lhs: smt.ExprRef, rhs: smt.ExprRef
) -> Optional[smt.ExprRef]:
    """
    Rewrite at root a single time.
    """
    subst = pmatch(t, vs, lhs)
    if subst is not None:
        return smt.substitute(rhs, *subst.items())
    return None


def apply(
    goal: smt.BoolRef, vs: list[smt.ExprRef], head: smt.BoolRef, body: smt.BoolRef
) -> smt.BoolRef:
    return rewrite1(goal, vs, head, body)


class Rule(NamedTuple):
    """A rewrite rule tuple"""

    vs: list[smt.ExprRef]
    lhs: smt.ExprRef
    rhs: smt.ExprRef


def rewrite(t: smt.ExprRef, rules: list[Rule]) -> smt.ExprRef:
    """
    Sweep through term once performing rewrites.
    """
    if smt.is_app(t):
        t = t.decl()(*[rewrite(arg, rules) for arg in t.children()])  # rewrite children
        for vs, lhs, rhs in rules:
            res = rewrite1(t, vs, lhs, rhs)
            if res is not None:
                t = res
    return t


def rule_of_theorem(thm: smt.BoolRef) -> Rule:
    """
    Unpack theorem of form `forall vs, lhs = rhs` into a Rule tuple
    """
    vs = []
    while smt.is_quantifier(thm):
        if thm.is_forall():
            vs1, thm = open_binder(thm)
            vs.extend(vs1)
        else:
            raise Exception("Not a universal quantifier", thm)
    if not smt.is_eq(thm):
        raise Exception("Not an equation", thm)
    lhs, rhs = thm.children()
    return Rule(vs, lhs, rhs)


def decl_index(rules: list[Rule]) -> dict[smt.FuncDeclRef, Rule]:
    """Build a dictionary of rules indexed by their lhs head function declaration."""
    return {lhs.decl(): (vs, lhs, rhs) for vs, lhs, rhs in rules}


def rewrite_star(t: smt.ExprRef, rules: list[Rule]) -> smt.ExprRef:
    """
    Repeat rewrite until no more rewrites are possible.
    """
    while True:
        t1 = rewrite(t, rules)
        if t1.eq(t):
            return t1
        t = t1


def open_binder(lam: smt.QuantifierRef) -> tuple[list[smt.ExprRef], smt.ExprRef]:
    """Open a quantifier with fresh variables"""
    # Open with capitalized names to match tptp conventions
    vars = [
        smt.Const(lam.var_name(i).upper(), lam.var_sort(i))
        for i in reversed(range(lam.num_vars()))
    ]
    return vars, smt.substitute_vars(lam.body(), *vars)


def occurs(x, t):
    """Does x occur in t?"""
    if smt.is_var(t):
        return x.eq(t)
    if smt.is_app(t):
        return any(occurs(x, t.arg(i)) for i in range(t.num_args()))
    return False


def unify_db(
    p1: smt.ExprRef, p2: smt.ExprRef
) -> Optional[dict[smt.ExprRef, smt.ExprRef]]:
    """Unification using de Bruijn indices as variables"""
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


def quant_kind_eq(t1: smt.ExprRef, t2: smt.ExprRef) -> bool:
    """Check both quantifiers are of the same kind"""
    return (
        t1.is_forall() == t2.is_forall()
        and t1.is_exists() == t2.is_exists()
        and t1.is_lambda() == t2.is_lambda()
    )


def alpha_eq(t1, t2):
    if t1.eq(t2):  # fast path
        return True
    elif smt.is_quantifier(t1):
        if (
            smt.is_quantifier(t2)
            and quant_kind_eq(t1, t2)
            and t1.num_vars() == t2.num_vars()
            and [t1.var_sort(i) == t2.var_sort(i) for i in range(t1.num_vars())]
        ):
            vs, body1 = open_binder(t1)
            body2 = smt.substitute_vars(t2.body(), *reversed(vs))
            return alpha_eq(body1, body2)
        else:
            return False
    elif smt.is_app(t1):
        if smt.is_app(t2) and t1.decl() == t2.decl():
            return all(alpha_eq(t1.arg(i), t2.arg(i)) for i in range(t1.num_args()))
        else:
            return False
    else:
        raise Exception(f"Unexpected terms in alpha_eq", t1, t2)
    # could instead maybe use a solver check or simplify tactic on Goal(t1 == t2)


class HornClause(NamedTuple):
    vs: list[smt.ExprRef]
    head: smt.BoolRef
    body: list[smt.BoolRef]


def horn_of_theorem(thm: smt.BoolRef) -> HornClause:
    """Unpack theorem of form `forall vs, body => head` into a HornClause tuple"""
    vs = []
    while smt.is_quantifier(thm):
        if thm.is_forall():
            vs1, thm = open_binder(thm)
            vs.extend(vs1)
        else:
            raise Exception("Not a universal quantifier", thm)
    if not smt.is_implies(thm):
        return HornClause(vs, thm, [])
    else:
        body, head = thm.children()
        if smt.is_and(body):
            body = list(body.children())
        else:
            body = [body]
        return HornClause(vs, head, body)


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
    """A generator of values for a sort. Repeatedly calls z3 to get a new value."""
    s = smt.Solver()
    x, y = smt.Consts("x y", sort)
    s.add(x == y)  # trick to actually have x in model
    if sort in kd.notation.wf.methods:
        s.add(kd.notation.wf(x))
    while s.check() == smt.sat:
        m = s.model()
        yield m.eval(x)
        s.add(x != m.eval(x))


def expr_to_lean(expr: smt.ExprRef):
    # TODO
    pass


def subterms(t: smt.ExprRef):
    """Generate all subterms of a term"""
    todo = [t]
    while len(todo) > 0:
        x = todo.pop()
        yield x
        todo.extend(x.children())


def sorts(t: smt.ExprRef):
    """Generate all sorts in a term"""
    for t in subterms(t):
        yield t.sort()


def decls(t: smt.ExprRef):
    """Return all function declarations in a term."""
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


import os
import glob
import inspect


def prompt(prompt: str):
    """
    Ask an AI.

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
