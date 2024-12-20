"""
Various term manipulation helpers. Pattern matchers, unifiers, rewriters, term orderings, etc.
"""

from kdrag.kernel import is_proof
import kdrag.smt as smt
import sys
import kdrag as kd
from typing import Optional, NamedTuple
from enum import Enum


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


def pmatch(
    vs: list[smt.ExprRef], pat: smt.ExprRef, t: smt.ExprRef, subst=None
) -> Optional[dict[smt.ExprRef, smt.ExprRef]]:
    """
    Pattern match t against pat considering vs as variables. Returns substitution dictionary if succeeds
    https://www.philipzucker.com/ho_unify/
    """
    if pat.sort() != t.sort():
        return None
    if subst is None:
        subst = {}
    todo = [(pat, t)]
    no_escape = []

    def is_var(x):
        return any(x.eq(v) for v in vs)

    def check_escape(x):
        if any(x.eq(v) for v in no_escape):
            return False
        else:
            return all(check_escape(c) for c in x.children())

    while todo:
        pat, t = todo.pop()
        if is_var(pat):  # regular pattern
            if pat in subst:
                if not alpha_eq(subst[pat], t):
                    return None
            else:
                if check_escape(t):  # check_escape is relative of occurs_check
                    subst[pat] = t
                else:
                    return None
        elif smt.is_select(pat) and is_var(pat.arg(0)):
            #  higher order pattern. "select" is smt speak for apply.
            # F[x,y,z] = t ---> F = Lambda([x,y,z], t)
            F = pat.arg(0)
            allowedvars = pat.children()[1:]
            """
            if any(
                v not in no_escape for v in allowedvars
            ):  # TODO: this is probably wrong
                raise Exception(
                    "Improper higher order pattern", pat
                )  # we could relax this to do syntactic unification here.
            """
            # By commenting this out, I've enabled non obviously bound constants
            # other option: Just lift them all out.
            # smt.subsitute(t, *[zip(a,a.FreshConst("")) for a for allowed_vars])
            t1 = smt.Lambda(allowedvars, t)
            todo.append((F, t1))
        elif smt.is_quantifier(pat):
            if (
                not smt.is_quantifier(t)
                or not quant_kind_eq(t, pat)
                or t.num_vars() != pat.num_vars()
            ):
                return None
            vs1, patbody = open_binder(pat)
            no_escape.extend(vs1)
            tbody = smt.substitute_vars(t.body(), *reversed(vs1))
            todo.append((patbody, tbody))
        elif smt.is_app(pat):
            if not smt.is_app(t) or pat.decl() != t.decl():
                return None
            todo.extend(zip(pat.children(), t.children()))
        else:
            raise Exception("Unexpected pattern", t, pat)
    return subst


def pmatch_rec(
    vs: list[smt.ExprRef], pat: smt.ExprRef, t: smt.ExprRef
) -> Optional[dict[smt.ExprRef, smt.ExprRef]]:
    todo = [t]
    while todo:
        t = todo.pop()
        subst = pmatch(vs, pat, t)
        if subst is not None:
            return subst
        elif smt.is_app(t):
            todo.extend(t.children())


def rewrite1(
    t: smt.ExprRef, vs: list[smt.ExprRef], lhs: smt.ExprRef, rhs: smt.ExprRef
) -> Optional[smt.ExprRef]:
    """
    Rewrite at root a single time.
    """
    subst = pmatch(vs, lhs, t)
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
    vs = [
        smt.FreshConst(lam.var_sort(i), prefix=lam.var_name(i).upper().split("!")[0])
        for i in range(lam.num_vars())
    ]
    return vs, smt.substitute_vars(lam.body(), *reversed(vs))


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


def is_subterm(t: smt.ExprRef, t2: smt.ExprRef) -> bool:
    if t.eq(t2):
        return True
    elif smt.is_app(t2):
        return any(is_subterm(t, c) for c in t2.children())
    else:
        return False


def sorts(t: smt.ExprRef):
    """Generate all sorts in a term"""
    for t in subterms(t):
        yield t.sort()


def decls(t: smt.ExprRef):
    """Return all function declarations in a term."""
    for t in subterms(t):
        if smt.is_app(t):
            yield t.decl()


def is_value(t: smt.ExprRef):
    return (
        smt.is_int_value(t)
        or smt.is_rational_value(t)
        or smt.is_algebraic_value(t)
        or smt.is_bv_value(t)
        or smt.is_true(t)
        or smt.is_false(t)
        or smt.is_string_value(t)
    )


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


class Order(Enum):
    EQ = 0  # Equal
    GR = 1  # Greater
    NGE = 2  # Not Greater or Equal


def lpo(vs: list[smt.ExprRef], t1: smt.ExprRef, t2: smt.ExprRef) -> Order:
    """
    Lexicographic path ordering.
    Based on https://www21.in.tum.de/~nipkow/TRaAT/programs/termorders.ML
    TODO add ordering parameter.
    """

    def is_var(x):
        return any(x.eq(v) for v in vs)

    if is_var(t2):
        if t1.eq(t2):
            return Order.EQ
        elif is_subterm(t2, t1):
            return Order.GR
        else:
            return Order.NGE
    elif is_var(t1):
        return Order.NGE
    elif smt.is_app(t1) and smt.is_app(t2):
        decl1, decl2 = t1.decl(), t2.decl()
        args1, args2 = t1.children(), t2.children()
        if all(lpo(vs, a, t2) == Order.NGE for a in args1):
            if decl1 == decl2:
                if all(lpo(vs, t1, a) == Order.GR for a in args2):
                    for a1, a2 in zip(args1, args2):
                        ord = lpo(vs, a1, a2)
                        if ord == Order.GR:
                            return Order.GR
                        elif ord == Order.NGE:
                            return Order.NGE
                    return Order.EQ
                else:
                    return Order.NGE
            elif (decl1.name(), decl1.get_id()) > (decl2.name(), decl2.get_id()):
                if all(lpo(vs, t1, a) == Order.GR for a in args2):
                    return Order.GR
                else:
                    return Order.NGE

            else:
                return Order.NGE
        else:
            return Order.GR
    else:
        raise Exception("Unexpected terms in lpo", t1, t2)


def kbo(vs: list[smt.ExprRef], t1: smt.ExprRef, t2: smt.ExprRef) -> Order:
    """
    Knuth Bendix Ordering, naive implementation.
    All weights are 1.
    Source: Term Rewriting and All That section 5.4.4
    """
    if t1.eq(t2):
        return Order.EQ

    def is_var(x):
        return any(x.eq(v) for v in vs)

    def vcount(t):
        todo = [t]
        vcount1 = {v: 0 for v in vs}
        while todo:
            t = todo.pop()
            if is_var(t):
                vcount1[t] += 1
            elif smt.is_app(t):
                todo.extend(t.children())
        return vcount1

    vcount1, vcount2 = vcount(t1), vcount(t2)
    if not all(vcount1[v] >= vcount2[v] for v in vs):
        return Order.NGE

    def weight(t):
        todo = [t]
        w = 0
        while todo:
            t = todo.pop()
            w += 1
            if smt.is_app(t):
                todo.extend(t.children())
        return w

    w1, w2 = weight(t1), weight(t2)
    if w1 > w2:
        return Order.GR
    elif w1 < w2:
        return Order.NGE
    else:
        if is_var(t2):  # KBO2a
            decl = t1.decl()
            if decl.arity() != 1:
                return Order.NGE
            while not t1.eq(t2):
                if t1.decl() != decl:
                    return Order.NGE
                else:
                    t1 = t1.arg(0)
            return Order.GR
        elif is_var(t1):
            return Order.NGE
        elif smt.is_app(t1) and smt.is_app(t2):
            decl1, decl2 = t1.decl(), t2.decl()
            if decl1 == decl2:  # KBO2c
                args1, args2 = t1.children(), t2.children()
                for a1, a2 in zip(args1, args2):
                    ord = kbo(vs, a1, a2)
                    if ord == Order.GR:
                        return Order.GR
                    elif ord == Order.NGE:
                        return Order.NGE
                raise Exception("Unexpected equality reached in kbo")
            elif (decl1.name(), decl1.get_id()) > (
                decl2.name(),
                decl2.get_id(),
            ):  # KBO2b
                return Order.GR
            else:
                return Order.NGE
        else:
            raise Exception("Unexpected terms in kbo", t1, t2)
