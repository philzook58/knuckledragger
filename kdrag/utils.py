"""
Various term manipulation helpers. Pattern matchers, unifiers, rewriters, term orderings, etc.
"""

from kdrag.kernel import is_proof
import kdrag.smt as smt
import sys
import kdrag as kd
from typing import Optional, Generator, Any
import os
import glob
import inspect


def open_binder(lam: smt.QuantifierRef) -> tuple[list[smt.ExprRef], smt.ExprRef]:
    """
    Open a quantifier with fresh variables. This achieves the locally nameless representation
    https://chargueraud.org/research/2009/ln/main.pdf
    where it is harder to go wrong.

    >>> x = smt.Int("x")
    >>> open_binder(smt.ForAll([x], x > 0))
    ([X!...], X!... > 0)
    """
    # Open with capitalized names to match tptp conventions
    vs = [
        smt.FreshConst(lam.var_sort(i), prefix=lam.var_name(i).upper().split("!")[0])
        for i in range(lam.num_vars())
    ]
    return vs, smt.substitute_vars(lam.body(), *reversed(vs))


def open_binder_unhygienic(
    lam: smt.QuantifierRef,
) -> tuple[list[smt.ExprRef], smt.ExprRef]:
    """
    Do not use this. Use `open_binder`. Opens a quantifier with unfresh variables.

    >>> x = smt.Int("x")
    >>> open_binder_unhygienic(smt.ForAll([x], x > 0))
    ([x], x > 0)
    """
    # Open with capitalized names to match tptp conventions
    vs = [smt.Const(lam.var_name(i), lam.var_sort(i)) for i in range(lam.num_vars())]
    return vs, smt.substitute_vars(lam.body(), *reversed(vs))


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
        elif smt.is_app(pat):
            nargs = pat.num_args()
            if not smt.is_app(t) or pat.decl() != t.decl():  # or nargs != t.num_args():
                return None
            for i in range(nargs):
                todo.append((pat.arg(i), t.arg(i)))
        elif isinstance(pat, smt.QuantifierRef):
            if (
                not isinstance(t, smt.QuantifierRef)
                or not quant_kind_eq(t, pat)
                or t.num_vars() != pat.num_vars()
                or any(t.var_sort(i) != pat.var_sort(i) for i in range(t.num_vars()))
            ):
                return None
            vs1, patbody = open_binder(pat)
            no_escape.extend(vs1)
            tbody = smt.substitute_vars(t.body(), *reversed(vs1))
            todo.append((patbody, tbody))
        else:
            raise Exception("Unexpected pattern", t, pat)
    return subst


def pmatch_fo(
    vs: list[smt.ExprRef], pat: smt.ExprRef, t: smt.ExprRef, subst=None
) -> Optional[dict[smt.ExprRef, smt.ExprRef]]:
    """
    First order pattern matching. Faster and simpler.
    Pattern match t against pat considering vs as variables. Returns substitution dictionary if succeeds

    >>> x, y = smt.Ints("x y")
    >>> pmatch_fo([x], x + x, y + y)
    {x: y}
    """
    if pat.sort() != t.sort():
        return None
    if subst is None:
        subst = {}
    todo = [(pat, t)]

    vids = [v.get_id() for v in vs]

    while todo:
        pat, t = todo.pop()
        if pat.get_id() in vids:
            if pat in subst:
                if not alpha_eq(subst[pat], t):
                    return None
            else:
                subst[pat] = t
        elif smt.is_app(pat):
            nargs = pat.num_args()
            if not smt.is_app(t) or pat.decl() != t.decl():
                return None
            for i in range(nargs):
                todo.append((pat.arg(i), t.arg(i)))
        else:
            raise Exception("Unexpected pattern", t, pat)
    return subst


def pmatch_rec(
    vs: list[smt.ExprRef], pat: smt.ExprRef, t: smt.ExprRef, into_binder=False
) -> Optional[tuple[smt.ExprRef, dict[smt.ExprRef, smt.ExprRef]]]:
    todo = [t]
    while todo:
        t = todo.pop()
        subst = pmatch(vs, pat, t)
        if subst is not None:
            return t, subst
        elif smt.is_app(t):
            todo.extend(t.children())
        elif (
            isinstance(t, smt.QuantifierRef) and into_binder
        ):  # going into the binder is dicey
            todo.append(t.body())


def unify(
    vs: list[smt.ExprRef], p1: smt.ExprRef, p2: smt.ExprRef
) -> Optional[dict[smt.ExprRef, smt.ExprRef]]:
    """Unification"""
    subst = {}
    todo = [(p1, p2)]

    def is_var(x):
        return any(x.eq(v) for v in vs)

    while todo:
        p1, p2 = todo.pop()  # we could pop _any_ of the todos, not just the top.
        if p1.eq(p2):  # delete
            continue
        elif is_var(p1):  # elim
            if occurs(p1, p2):
                return None
            todo = [
                (smt.substitute(t1, (p1, p2)), smt.substitute(t2, (p1, p2)))
                for (t1, t2) in todo
            ]
            subst = {k: smt.substitute(v, (p1, p2)) for k, v in subst.items()}
            subst[p1] = p2
        elif is_var(p2):  # orient
            todo.append((p2, p1))
        elif smt.is_app(p1):  # decompose
            if not smt.is_app(p2) or p1.decl() != p2.decl():
                return None
            todo.extend(zip(p1.children(), p2.children()))
        else:
            raise Exception("unexpected case", p1, p2)
    return subst


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


def free_in(vs: smt.ExprRef, t: smt.ExprRef) -> bool:
    """
    Returns True if none of the variables in vs exist unbound in t.

    >>> x,y,z = smt.Ints("x y z")
    >>> assert not free_in(x, x + y + z)
    >>> assert free_in(x, y + z)
    >>> assert free_in(x, smt.Lambda([x], x + y + z))
    """
    return smt.Lambda(vs, t).body().eq(t)


def occurs(x: smt.ExprRef, t: smt.ExprRef) -> bool:
    """Does x occur in t?

    >>> x,y,z = smt.Ints("x y z")
    >>> assert occurs(x + y, x + y + z)
    >>> assert not occurs(x + y, x + z)
    >>> assert occurs(x, x + y + z)
    >>> v0 = smt.Var(0, smt.IntSort())
    >>> assert occurs(v0, v0 + x + y)
    """
    # TODO: Not alpha invariant, doesn't handle binders
    if x.eq(t):
        return True
    elif smt.is_app(t):
        return any(occurs(x, t.arg(i)) for i in range(t.num_args()))
    elif smt.is_quantifier(t):
        raise Exception("occurs check quantifier unimplemented", t)
    elif smt.is_var(t):
        return False
    else:
        raise Exception("Unexpected term in occurs check", t)


# TODO: is_subterm and occurs are duplicated


def is_subterm(t: smt.ExprRef, t2: smt.ExprRef) -> bool:
    """
    TODO: Not alpha invariant or going into binders
    """
    if t.eq(t2):
        return True
    elif smt.is_app(t2):
        return any(is_subterm(t, c) for c in t2.children())
    else:
        return False


def quant_kind_eq(t1: smt.QuantifierRef, t2: smt.QuantifierRef) -> bool:
    """Check both quantifiers are of the same kind

    >>> x = smt.Int("x")
    >>> forall = smt.ForAll([x], x > 0)
    >>> exists = smt.Exists([x], x > 0)
    >>> lamb = smt.Lambda([x], x > 0)
    >>> assert quant_kind_eq(forall, forall)
    >>> assert quant_kind_eq(exists, exists)
    >>> assert quant_kind_eq(lamb, lamb)
    >>> assert not quant_kind_eq(forall, exists)
    """
    # TODO: could make a faster version using Z3 kind tags
    return (
        t1.is_forall() == t2.is_forall()
        and t1.is_exists() == t2.is_exists()
        and t1.is_lambda() == t2.is_lambda()
    )


def alpha_eq(t1, t2):
    """
    Alpha equivalent equality.
    Z3's fast built-in t.eq is not alpha invariant.

    >>> x,y = smt.Ints("x y")
    >>> t1,t2 = smt.Lambda([x], x), smt.Lambda([y], y)
    >>> t1.eq(t2) # syntactic equality
    False
    >>> alpha_eq(t1, t2)
    True
    >>> alpha_eq(smt.Lambda([x], x)[3], smt.IntVal(3)) # No beta equivalence
    False
    """
    if t1.eq(t2):  # fast path
        return True
    # elif (smt.is_ground(t1) or smt.is_ground(t2)) and not t1.eq(t2): TODO: Needs is_ground threaded up from C API to python API.
    #    return False
    elif smt.is_quantifier(t1):
        if (
            smt.is_quantifier(t2)
            and quant_kind_eq(t1, t2)
            and t1.num_vars() == t2.num_vars()
            and [t1.var_sort(i) == t2.var_sort(i) for i in range(t1.num_vars())]
        ):
            # It is ok to keep de bruijn indices here and not use open_binder?
            # vs, body1 = open_binder(t1)
            # body2 = smt.substitute_vars(t2.body(), *reversed(vs))
            # return alpha_eq(body1, body2)
            return alpha_eq(t1.body(), t2.body())
        else:
            return False
    elif smt.is_app(t1):
        if smt.is_app(t2) and t1.decl() == t2.decl():
            return all(alpha_eq(t1.arg(i), t2.arg(i)) for i in range(t1.num_args()))
        else:
            return False
    elif smt.is_var(t1):
        return (
            smt.is_var(t2)
            and smt.get_var_index(t1) == smt.get_var_index(t2)
            and t1.sort() == t2.sort()
        )  # sort check is probably redundant if quantifier bound?
    else:
        raise Exception("Unexpected terms in alpha_eq", t1, t2)
    # could instead maybe use a solver check or simplify tactic on Goal(t1 == t2)


def generate(sort: smt.SortRef, pred=None) -> Generator[smt.ExprRef, None, None]:
    """
    A generator of values for a sort. Repeatedly calls z3 to get a new value.

    >>> set(generate(smt.BoolSort()))
    {True, False}
    >>> sorted([v.as_long() for v in generate(smt.IntSort(), pred=lambda x: smt.And(0 <= x, x < 5))])
    [0, 1, 2, 3, 4]
    >>> import itertools
    >>> len(list(itertools.islice(generate(smt.ArraySort(smt.IntSort(), smt.IntSort())), 3)))
    3
    """
    s = smt.Solver()
    x, y = smt.Consts("x y", sort)
    s.add(x == y)  # trick to actually have x in model
    if pred is not None:
        s.add(pred(x))
    if sort in kd.notation.wf.methods:
        s.add(kd.notation.wf(x))
    while s.check() == smt.sat:
        m = s.model()
        yield m.eval(x)
        s.add(x != m.eval(x))


def all_values(*es: smt.ExprRef) -> Generator[list[smt.ExprRef], None, None]:
    """
    Generate all values possible for an expression. Generator won't terminate if there are infinite possible values.
    Concretization.

    >>> assert set(all_values(smt.If(smt.Bool("x"), 2, 3))) == {smt.IntVal(2), smt.IntVal(3)}
    """
    s = smt.Solver()
    es1 = [smt.FreshConst(e.sort(), prefix="e") for e in es]
    for e, e1 in zip(es, es1):
        s.add(e1 == e)
    while True:
        res = s.check()
        if res == smt.unsat:
            return
        elif res == smt.sat:
            m = s.model()
            vs = [m.eval(e) for e in es]
            yield vs[0] if len(vs) == 1 else vs
            for e, v in zip(es1, vs):
                s.add(e != v)
        else:
            raise ValueError("Solver unknown in values", es)


"""
def expr_to_lean(expr: smt.ExprRef):
    # TODO
    pass
"""


def free_vars(t: smt.ExprRef) -> set[smt.ExprRef]:
    """
    Return free variables in an expression. Looks at kernel.defns to determine if contacts are free.
    If you have meaningful constants no registered there, this may not work.

    >>> x,y = smt.Ints("x y")
    >>> free_vars(smt.Lambda([x], x + y + 1))
    {y}
    """
    fvs = set()
    todo = [t]
    while todo:
        t = todo.pop()
        if smt.is_var(t) or is_value(t) or smt.is_constructor(t):
            continue
        if smt.is_const(t) and t.decl() not in kd.kernel.defns:
            fvs.add(t)
        elif isinstance(t, smt.QuantifierRef):
            todo.append(t.body())
        elif smt.is_app(t):
            todo.extend(t.children())
    return fvs


def sanity_check_consistency(thms: list[smt.ExprRef | kd.kernel.Proof], timeout=1000):
    """
    Sanity check theorems or proofs for consistency. If they are inconsistent, raise an error.
    Otherwise, return the result of the check. A sat result shows consistency, but an unknown result does not imply anything.

    It may be nice to try and apply this function to your axioms or theory in CI.

    >>> x,y = smt.Ints("x y")
    >>> sanity_check_consistency([x == y])
    sat
    """
    s = smt.Solver()
    s.set("timeout", timeout)
    for thm in thms:
        if isinstance(thm, kd.kernel.Proof):
            s.add(thm.thm)
        elif isinstance(thm, smt.ExprRef):
            s.add(thm)
        else:
            raise ValueError(
                "Unsupported type in `thms` for consistency_sanity_check function"
            )
    res = s.check()
    if res == smt.unsat:
        raise ValueError("Theorems are inconsistent", thms)
    else:
        return res


def prune(
    thm: smt.BoolRef | smt.QuantifierRef | kd.kernel.Proof, by=[], timeout=1000
) -> list[smt.ExprRef | kd.kernel.Proof]:
    """
    Prune the theorems used using unsat core. Helpful to speedup future proof verification.

    >>> p,q,r = smt.Bools("p q r")
    >>> sorted(prune(p & q, [p, q, r]), key=lambda b: b.decl().name())
    [p, q]
    """
    s = smt.Solver()
    s.set("timeout", timeout)
    for n, p in enumerate(by):
        if isinstance(p, smt.ExprRef):
            s.assert_and_track(p, "KNUCKLEBY_{}".format(n))
        elif kd.kernel.is_proof(p):
            s.assert_and_track(p.thm, "KNUCKLEBY_{}".format(n))
        else:
            raise ValueError("Unsupported type in `by` for prune function")
    s.assert_and_track(smt.Not(thm), "KNUCKLEGOAL")
    res = s.check()
    if res == smt.sat:
        raise ValueError("Theorem is not valid")
    elif res == smt.unknown:
        raise ValueError("Solver confused or timed out")
    elif res == smt.unsat:
        core = s.unsat_core()
        used = []
        for c in core:
            name = c.decl().name()
            if name.startswith("KNUCKLEBY_"):
                idx = int(name.split("_")[-1])
                used.append(by[idx])
        if smt.Bool("KNUCKLEGOAL") not in core:
            raise ValueError("Hypotheses are inconsistent", used)
        return used
    else:
        raise ValueError("Unexpected solver response")


def subterms(t: smt.ExprRef, into_binder=False):
    """Generate all subterms of a term

    >>> x,y = smt.Ints("x y")
    >>> list(subterms(x + y == y))
    [x + y == y, y, x + y, y, x]
    >>> list(subterms(smt.ForAll([x], x + y == y)))
    [ForAll(x, x + y == y)]
    >>> list(subterms(smt.ForAll([x], x + y == y), into_binder=True))
    [ForAll(x, x + y == y), Var(0) + y == y, y, Var(0) + y, y, Var(0)]
    """
    todo = [t]
    while len(todo) > 0:
        x = todo.pop()
        yield x
        if smt.is_app(x):
            todo.extend(x.children())
        elif isinstance(x, smt.QuantifierRef) and into_binder:
            todo.append(x.body())


def sorts(t: smt.ExprRef):
    """Generate all sorts in a term"""
    for t in subterms(
        t, into_binder=True
    ):  # TODO: May want to get sorts of quantified variables that don't appear in bodies.
        yield t.sort()


def decls(t: smt.ExprRef) -> set[smt.FuncDeclRef]:
    """Return all function declarations in a term."""
    return {e.decl() for e in subterms(t, into_binder=True) if smt.is_app(e)}


def is_value(t: smt.ExprRef):
    # TODO, could make faster check using Z3 internals
    return (
        smt.is_int_value(t)
        or smt.is_rational_value(t)
        or smt.is_algebraic_value(t)
        or smt.is_bv_value(t)
        or smt.is_true(t)
        or smt.is_false(t)
        or smt.is_string_value(t)
        or smt.is_fp_value(t)
        or smt.is_fprm_value(t)
        or (smt.is_constructor(t) and all(is_value(c) for c in t.children()))
    )


def ast_size_sexpr(t: smt.AstRef) -> int:
    """
    Get an approximate size of an AST node by its s-expression length.
    This is probably faster than any python layer traversal one can do.
    Pretty printed ast size will be correlated to expression size, maybe even DAG size,
    since Z3 inserts `let`s to avoid duplication.

    >>> ast_size_sexpr(smt.Int("x"))
    1
    >>> ast_size_sexpr(smt.Int("x") + smt.Int("y"))
    7
    """
    return len(t.sexpr())


def lemma_db() -> dict[str, kd.kernel.Proof]:
    """Scan all modules for Proof objects and return a dictionary of them."""
    db: dict[str, kd.kernel.Proof] = {}
    for modname, mod in sys.modules.items():
        for name, thm in mod.__dict__.items():
            if is_proof(thm):
                db[modname + "." + name] = thm
            elif (
                isinstance(thm, smt.SortRef)
                or isinstance(thm, smt.FuncDeclRef)
                or isinstance(thm, smt.ExprRef)
            ):
                for name2, thm2 in thm.__dict__.items():
                    if is_proof(thm2):
                        db[modname + "." + name + "." + name2] = thm2
            # TODO: Scan GenericProof, SortDispatch objects, objects.
            # TODO: Not a problem at the moment, but we should cache unchanged modules.
            # TODO: Maybe scan user module specially.
            # TODO: Dedup repeated theorems
    return db


def search_expr(
    e: smt.ExprRef, pfs: dict[object, kd.kernel.Proof]
) -> dict[tuple[str, kd.kernel.Proof], Any]:
    """
    Search for expressions in the proof database that match `e` using pattern matching.

    >>> x,z = smt.Ints("x z")
    >>> search_expr(z + 0, {\
        "thm1": kd.prove(smt.ForAll([x], x + 0 == x)),\
        "thm2" : kd.prove(z + 0 == z),\
        "thm3" : kd.prove(smt.ForAll([x], x + 1 == 1 + x)),\
        "thm4" : kd.prove(smt.BoolVal(True))})
    {('thm1', |- ForAll(x, x + 0 == x)): [z], ('thm2', |- z + 0 == z): []}
    """
    found = {}
    # Hmm. This isn't that different from the implementation of rewrite itself...
    for name, pf in pfs.items():
        try:  # try to convert to rewrite rule
            rule = kd.rewrite.rewrite_of_expr(pf.thm)
            t_subst = kd.utils.pmatch_rec(rule.vs, rule.lhs, e, into_binder=True)
            if t_subst is None:
                if (
                    smt.is_const(rule.rhs) and rule.rhs not in kd.kernel.defns
                ):  # Lots of trivial rules that match `== x`
                    continue
                t_subst = kd.utils.pmatch_rec(rule.vs, rule.rhs, e, into_binder=True)
            if t_subst is not None:
                _, subst = t_subst
                try:
                    found[(name, pf)] = [subst.get(v) for v in rule.vs]
                except Exception as _:
                    raise Exception(name, pf)
        except kd.rewrite.RewriteRuleException as _:
            pass
    # TODO: Sort `found` by some criteria
    return found


def search_decl(
    f: smt.FuncDeclRef, db: dict[object, kd.kernel.Proof]
) -> dict[tuple[str, kd.kernel.Proof], Any]:
    """
    Search for declarations in the proof database that contain function declaration f
    """
    found = {}
    for name, pf in db.items():
        if kd.kernel.is_proof(pf) and f in kd.utils.decls(pf.thm):
            found[(name, pf)] = ()
    return found


def search(
    *es: smt.FuncDeclRef | smt.ExprRef, db: dict[Any, kd.kernel.Proof] = {}
) -> dict[tuple[str, kd.kernel.Proof], Any]:
    """
    Search for function declarations or expressions.
    Takes intersection of found results if given multiple arguments.
    Builds a database by scanning loaded modules by default.
    """
    if len(db) == 0:
        db = kd.utils.lemma_db()
    results = []
    for e in es:
        if isinstance(e, smt.FuncDeclRef):
            results.append(search_decl(e, db))
        elif isinstance(e, smt.ExprRef):
            results.append(search_expr(e, db))
        else:
            raise ValueError("Unsupported type for search", e)
    return {k: v for k, v in results[0].items() if all(k in db for db in results)}


def prompt(prompt: str):
    """
    Ask an AI.

    Get the root directory of the current package, find all .py files within
    that directory, and concatenate their contents into a single string separated by `---`.

    Returns:
        str: A single string with all .py files concatenated, separated by `---`.
    """
    excluded_subdirs = ["eprover"]
    current_file = inspect.getfile(inspect.currentframe())  # type: ignore      this is insanely hacky anyway
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


def antipattern(xs: list[smt.ExprRef]) -> tuple[list[smt.ExprRef], smt.ExprRef]:
    """
    Anti pattern matching. Given a list of concrete examples, return the most specific pattern that matches them all.
    Returns tuple of list of pattern variables and pattern expression.

    https://arxiv.org/pdf/2302.00277 Anti-unification and Generalization: A Survey
    https://arxiv.org/abs/2212.04596  babble: Learning Better Abstractions with E-Graphs and Anti-Unification
    https://ericlippert.com/2018/10/29/anti-unification-part-1/


    >>> a,b,c,d = smt.Ints("a b c d")
    >>> f = smt.Function("f", smt.IntSort(), smt.IntSort(), smt.IntSort())
    >>> g = smt.Function("g", smt.IntSort(), smt.IntSort(), smt.IntSort())
    >>> t1 = f(a,g(a,b))
    >>> t2 = f(c,g(c,d))
    >>> t3 = f(a,g(d,b))
    >>> antipattern([t1,t2])
    ([a!..., b!...], f(a!..., g(a!..., b!...)))
    >>> antipattern([t1,t2,t3])
    ([a!..., a!..., b!...], f(a!..., g(a!..., b!...)))

    """
    # we should key on the tuple of all terms, because we want to return same variable.
    sort = xs[0].sort()
    assert all(
        x.sort() == sort for x in xs
    )  # asking to antiunify terms of different sorts is invalid

    # antisubst is a dictionary that maps tuples of terms to a new variable
    antisubst: dict[tuple[smt.ExprRef, ...], smt.ExprRef] = {}

    def worker(xs):
        x0 = xs[0]
        if all(x.eq(x0) for x in xs):
            return x0
        elif xs in antisubst:
            return antisubst[xs]
        elif all(smt.is_app(x) for x in xs):
            decl, nargs = x0.decl(), x0.num_args()
            if all(decl == x.decl() and nargs == x.num_args() for x in xs):
                args = []
                for bs in zip(*[x.children() for x in xs]):
                    args.append(worker(bs))
                return decl(*args)
            else:
                z = smt.FreshConst(x0.sort(), prefix=decl.name())
                antisubst[xs] = z
                return z
        else:
            raise Exception("Unexpected case in antipattern", xs)

    res = worker(tuple(xs))
    return list(antisubst.values()), res
