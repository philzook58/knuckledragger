"""
Various term manipulation helpers. Pattern matchers, unifiers, rewriters, term orderings, etc.
"""

from kdrag.kernel import is_proof
import kdrag.smt as smt
import sys
import kdrag as kd
from typing import Optional, Callable, no_type_check, Generator
import fractions
import functools
import operator
from collections import namedtuple
import os
import glob
import inspect


def open_binder(lam: smt.QuantifierRef) -> tuple[list[smt.ExprRef], smt.ExprRef]:
    """Open a quantifier with fresh variables"""
    # Open with capitalized names to match tptp conventions
    vs = [
        smt.FreshConst(lam.var_sort(i), prefix=lam.var_name(i).upper().split("!")[0])
        for i in range(lam.num_vars())
    ]
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
        elif isinstance(pat, smt.QuantifierRef):
            if (
                not isinstance(t, smt.QuantifierRef)
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


def occurs(x: smt.ExprRef, t: smt.ExprRef) -> bool:
    """Does x occur in t?"""
    if smt.is_var(t):
        return x.eq(t)
    if smt.is_app(t):
        return any(occurs(x, t.arg(i)) for i in range(t.num_args()))
    return False


def quant_kind_eq(t1: smt.QuantifierRef, t2: smt.QuantifierRef) -> bool:
    """Check both quantifiers are of the same kind"""
    return (
        t1.is_forall() == t2.is_forall()
        and t1.is_exists() == t2.is_exists()
        and t1.is_lambda() == t2.is_lambda()
    )


def alpha_eq(t1, t2):
    """
    Alpha equivalent equality.

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


"""
def expr_to_lean(expr: smt.ExprRef):
    # TODO
    pass
"""


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


def lemma_db():
    """Scan all modules for Proof objects and return a dictionary of them."""
    db = {}
    for modname, mod in sys.modules.items():
        thms = {name: thm for name, thm in mod.__dict__.items() if is_proof(thm)}
        if len(thms) > 0:
            db[modname] = thms
    return db


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


@functools.cache
def namedtuple_of_constructor(sort: smt.DatatypeSortRef, idx: int):
    """
    Given a datatype sort and an index, return a named tuple with field names and the constructor.
    >>> Nat = smt.Datatype("Nat")
    >>> Nat.declare("Z")
    >>> Nat.declare("S", ("pred", Nat))
    >>> Nat = Nat.create()
    >>> namedtuple_of_constructor(Nat, 1)(0)
    S(pred=0)
    """
    decl = sort.constructor(idx)
    fields = [sort.accessor(idx, i).name() for i in range(decl.arity())]
    return namedtuple(decl.name(), fields)


# could env be just a python module? That's kind of intriguing


# This is fiendishly difficult to typecheck probably
@no_type_check
def eval_(e: smt.ExprRef, globals={}):
    """
    Evaluate a z3 expression in a given environment. The analog of python's `eval`.

    >>> eval_(smt.IntVal(42))
    42
    >>> eval_(smt.IntVal(1) + smt.IntVal(2))
    3
    >>> x = smt.Int("x")
    >>> eval_(smt.Lambda([x], x + 1)[3])
    4
    >>> R = kd.Record("R", ("x", kd.Z), ("y", smt.BoolSort()))
    >>> eval_(R(42, True).x)
    42
    >>> eval_(R(42,True).is_R)
    True
    """
    if isinstance(e, smt.QuantifierRef):
        if e.is_lambda():
            vs, body = open_binder(e)
            # also possibly lookup Lambda in globals.
            # and/or use KnuckleClosure.
            return lambda *args: eval_(
                body, {**{v.decl().name(): arg for v, arg in zip(vs, args)}, **globals}
            )
        else:
            raise ValueError("Quantifier not implemented", e)
    elif isinstance(e, smt.IntNumRef):  # smt.is_int_value(e):
        return e.as_long()
    elif isinstance(e, smt.RatNumRef):
        return fractions.Fraction(e.numerator_as_long(), e.denominator_as_long())
    elif isinstance(e, smt.FPNumRef):
        raise ValueError("FPNumRef not implemented")
    elif smt.is_app(e):
        if smt.is_if(e):
            c = eval_(e.arg(0), globals=globals)
            if isinstance(c, bool):
                if c:
                    return eval_(e.arg(1), globals=globals)
                else:
                    return eval_(e.arg(2), globals=globals)
            elif isinstance(c, smt.ExprRef):
                return smt.If(
                    c,
                    eval_(e.arg(1), globals=globals),
                    eval_(e.arg(2), globals=globals),
                )
            else:
                # possibly lookup "If" in environment
                raise ValueError("If condition not a boolean or expression", c)

        children = list(map(lambda x: eval_(x, globals), e.children()))
        decl = e.decl()
        if decl in kd.kernel.defns:
            defn = kd.kernel.defns[e.decl()]
            # Fresh vars and add to context?
            # e1 = z3.substitute(defn.body, *zip(defn.args, e.children()))
            f = eval_(smt.Lambda(defn.args, defn.body), globals=globals)
            return f(*children)
            # return eval_(
            #    smt.Select(smt.Lambda(defn.args, defn.body), *children), globals=globals
            # )
            # return eval_(env, e1)
        elif decl.name() in globals:
            # hasattr(globals[decl.name()], "__call__")?
            if smt.is_const(e):
                return globals[decl.name()]
            else:
                return globals[decl.name()](*children)
        elif smt.is_accessor(e):
            # return children[0][decl.name()]
            return getattr(children[0], e.decl().name())
        elif smt.is_select(e):  # apply
            return children[0](*children[1:])
        # elif is_store(e): hmm
        #    #return children[0]._replace(children[1], children[2])
        elif smt.is_const_array(e):
            return lambda x: children[0]  # Maybe return a Closure here?
        elif smt.is_map(e):
            return map(children[0], children[1])
        elif smt.is_constructor(e):
            sort, decl = e.sort(), e.decl()
            i = 0  # Can't have 0 constructors. Makes typechecker happy
            for i in range(sort.num_constructors()):
                if e.decl() == sort.constructor(i):
                    break
            cons = namedtuple_of_constructor(sort, i)
            return cons(*children)
        elif isinstance(e, smt.BoolRef):
            if smt.is_true(e):
                return True
            elif smt.is_false(e):
                return False
            elif smt.is_and(e):
                return functools.reduce(operator.and_, children)
            elif smt.is_or(e):
                return functools.reduce(operator.or_, children)
            elif smt.is_not(e):
                return ~children[0]
            elif smt.is_implies(e):
                return (~children[0]) | children[1]
            elif smt.is_eq(e):
                return children[0] == children[1]
            elif smt.is_lt(e):
                return children[0] < children[1]
            elif smt.is_le(e):
                return children[0] <= children[1]
            elif smt.is_ge(e):
                return children[0] >= children[1]
            elif smt.is_gt(e):
                return children[0] > children[1]
            elif smt.is_recognizer(e):
                sort = e.arg(0).sort()
                decl = e.decl()
                name = None
                for i in range(sort.num_constructors()):
                    if e.decl() == sort.recognizer(i):
                        name = sort.constructor(i).name()
                assert name is not None
                if type(children[0]).__name__ == name:
                    return True
                else:
                    return False
            else:
                raise ValueError("Unknown bool expression", e)
        # elif smt.is_string_value(e):
        #    return e.as_string()
        # elif isisntance(e, ArithRef):
        elif smt.is_add(e):
            return sum(children)
        elif smt.is_mul(e):
            return functools.reduce(operator.mul, children)
        elif smt.is_sub(e):
            return children[0] - children[1]
        elif smt.is_div(e):
            return children[0] / children[1]
        elif smt.is_idiv(e):
            return children[0] // children[1]
        elif smt.is_power(e):
            return children[0] ** children[1]
        elif smt.is_mod(e):
            return children[0] % children[1]
        else:
            # we could raise error, or just return the expression itself (object | ExprRef) semantics
            raise ValueError("Unknown app expression type", e)
    else:
        raise ValueError("Unknown expression type", e)


def reify(s: smt.SortRef, x: object) -> smt.ExprRef:
    """
    sort directed reification of a python value. https://en.wikipedia.org/wiki/Normalisation_by_evaluation
    >>> reify(smt.IntSort(), 42)
    42
    >>> reify(smt.IntSort(), 42).sort()
    Int
    >>> x = smt.Int("x")
    >>> alpha_eq(reify(smt.ArraySort(smt.IntSort(), smt.IntSort()), lambda x: x + 1), smt.Lambda([x], x + 1))
    True
    >>> reify(smt.RealSort(), fractions.Fraction(10,16))
    5/8
    """
    if isinstance(x, smt.ExprRef):
        if x.sort() != s:
            raise ValueError(f"Sort mismatch of {x} : {x.sort()} != {s}")
        return x  # Although if we deeply modelled smt inside smt, maybe we'd want to quote here.
    elif isinstance(s, smt.ArraySortRef):
        # TODO: Probably not right, also not dealing with multi arg lambdas.
        if isinstance(x, Callable):
            v = smt.FreshConst(s.domain())
            y = x(v)
            assert y.sort() == s.range()
            return smt.Lambda([v], y)
        else:
            raise ValueError(f"Cannot call {x} as an array sort {s}")
    elif isinstance(s, smt.DatatypeSortRef):
        if isinstance(x, tuple):
            for i in range(s.num_constructors()):
                decl = s.constructor(i)
                if decl.name() == type(x).__name__:
                    arity = decl.arity()
                    assert len(x) == arity
                    return decl(*[reify(decl.domain(j), x[j]) for j in range(arity)])
            raise ValueError(f"Cannot reify {x} as a datatype {s}")
        raise ValueError("Reification on datatypesort not yet implemented")
    elif s == smt.IntSort():
        return smt.IntVal(x)
    elif s == smt.RealSort():
        return smt.RealVal(x)
    elif s == smt.BoolSort():
        return smt.BoolVal(x)
    elif s == smt.StringSort():
        return smt.StringVal(x)
    else:
        raise ValueError(f"Cannot reify {x} as an expression")
