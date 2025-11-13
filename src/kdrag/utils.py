"""
Various term manipulation helpers. Pattern matchers, unifiers, rewriters, term orderings, etc.
"""

from kdrag.kernel import is_proof
import kdrag.smt as smt
import sys
import kdrag as kd
from typing import Optional, Generator, Any, Callable, Sequence
import os
import glob
import inspect
from dataclasses import dataclass
from collections import defaultdict


def open_binder(lam: smt.QuantifierRef) -> tuple[list[smt.ExprRef], smt.ExprRef]:
    """
    Open a quantifier with fresh variables. This achieves the locally nameless representation
    https://chargueraud.org/research/2009/ln/main.pdf
    where it is harder to go wrong.

    The variables are schema variables which when used in a proof may be generalized

    >>> x = smt.Int("x")
    >>> open_binder(smt.ForAll([x], x > 0))
    ([X!...], X!... > 0)
    """
    # Open with capitalized names to match tptp conventions
    vs = [
        # smt.FreshConst(lam.var_sort(i), prefix=lam.var_name(i).upper().split("!")[0])
        kd.kernel.FreshVar(lam.var_name(i).upper().split("!")[0], lam.var_sort(i))
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


def pathmap(
    function: Callable[[smt.ExprRef], smt.ExprRef],
    e: smt.ExprRef,
    path: Optional[list[int]],
) -> smt.ExprRef:
    """
    Apply function at position in term
    >>> x,y,z = smt.Ints("x y z")
    >>> pathmap(lambda t: t + 1, x + y * z, [1,0])
    x + (y + 1)*z
    """
    if path:
        args = e.children()
        args = (
            args[: path[0]]
            + [pathmap(function, args[path[0]], path[1:])]
            + args[path[0] + 1 :]
        )
        return e.decl()(*args)
    else:
        return function(e)


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


def eunify(
    vs: list[smt.ExprRef], goal: smt.BoolRef, term_gen_heuristic=None
) -> Optional[tuple[dict[smt.ExprRef, smt.ExprRef], Optional[smt.BoolRef]]]:
    """
    Bottom up E-unification.
    Returns a substitution and remaining constraint. It is possible it makes no progress.

    https://www.philipzucker.com/smt_unify/
    >>> x,y,z = smt.Ints("x y z")
    >>> eunify([x,y], smt.And(x + 1 == y, y + 1 == 3))
    ({x: 1, y: 2}, None)
    >>> eunify([x,y,z], smt.And(x + y == z + 3*x, z + 1 + y == 3))
    ({z: -2*x + y}, -2*x + 2*y == 2)
    """
    # check that the goal is even solvable at all
    s = smt.Solver()
    s.add(goal)
    res = s.check()
    if res == smt.unsat:
        return None
    elif res == smt.unknown:
        raise Exception("eunify: SMT solver returned unknown")
    assert res == smt.sat
    # solve for ground constants first
    m = s.model()
    guesses = [smt.Eq(v, m.eval(v)) for v in vs if not v.eq(m.eval(v))]
    eqs = kd.utils.propagate(guesses, goal)
    subst = {eq.arg(0): eq.arg(1) for eq in eqs}
    goal = smt.substitute(goal, list(subst.items()))
    # Now guess seed expressions from the goal
    guess_ts = set(kd.utils.subterms(goal))
    # simplify can sometimes generate new subterms (reassociation etc). Questionably useful
    guess_ts.update(kd.utils.subterms(smt.simplify(goal)))
    # Could perhaps call some z3.Tactics here to generate more terms
    if term_gen_heuristic is not None:
        guess_ts.update(term_gen_heuristic(vs, goal))
    guesses = [
        smt.Eq(v, t)
        for t in guess_ts
        for v in vs
        if t.sort() == v.sort() and kd.utils.free_in([v], t)
    ]
    eqs = kd.utils.propagate(guesses, goal)
    while eqs:
        eq = eqs.pop()
        v, t = eq.children()
        if v not in subst and kd.utils.free_in(
            [v], t
        ):  # is it possible for free_in to fail? But it to eventually not fail?
            subst[v] = t
            eqs = [smt.substitute(m, (v, t)) for m in eqs if not m.arg(0).eq(v)]
    remainder_constraint = smt.simplify(smt.substitute(goal, *subst.items()))
    return subst, remainder_constraint if not smt.is_true(
        remainder_constraint
    ) else None


def free_in(vs: list[smt.ExprRef], t: smt.ExprRef) -> bool:
    """
    Returns True if none of the variables in vs exist unbound in t.
    Distinct from `occurs` in that vs have to be constants, not general terms.

    >>> x,y,z = smt.Ints("x y z")
    >>> assert not free_in([x], x + y + z)
    >>> assert free_in([x], y + z)
    >>> assert free_in([x], smt.Lambda([x], x + y + z))
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


def is_subterm(t: smt.ExprRef, t2: smt.ExprRef) -> bool:
    """
    TODO: Not alpha invariant or going into binders
    """
    return occurs(t, t2)


def is_strict_subterm(t: smt.ExprRef, t2: smt.ExprRef) -> bool:
    return not t.eq(t2) and is_subterm(t, t2)


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


def alpha_norm(expr: smt.ExprRef) -> smt.ExprRef:
    """
    Recursively rename all variables in an expression to canonical names.
    Printed form may become ambiguous because internally de Bruijn indices are used.

    >>> x,y,z,w = smt.Consts("x y z w", smt.IntSort())
    >>> p = smt.Real("p")
    >>> assert not smt.Lambda([x,y], x + y).eq(smt.Lambda([z,w], z + w))
    >>> assert alpha_norm(smt.Lambda([x,y], x + y)).eq(alpha_norm(smt.Lambda([z,w], z + w)))
    >>> _ = kd.prove(alpha_norm(smt.Lambda([x,p], p)) == smt.Lambda([x,p], p))
    """

    if isinstance(expr, smt.QuantifierRef):
        body = alpha_norm(expr.body())
        vs = [smt.Const("x" + str(i), expr.var_sort(i)) for i in range(expr.num_vars())]
        assert kd.utils.free_in(vs, body)
        body = smt.substitute_vars(body, *reversed(vs))
        if expr.is_forall():
            return smt.ForAll(vs, body)
        elif expr.is_exists():
            return smt.Exists(vs, body)
        elif expr.is_lambda():
            return smt.Lambda(vs, body)
        else:
            raise NotImplementedError("Unknown quantifier type")
    elif smt.is_app(expr):
        return expr.decl()(*map(alpha_norm, expr.children()))
    elif smt.is_var(expr):
        return expr
    else:
        raise NotImplementedError("Unknown expression type in alpha_norm", expr)


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


def propagate(maybes: list[smt.BoolRef], known: smt.BoolRef) -> list[smt.BoolRef]:
    """
    Prune the list of maybes to the ones implies by known

    >>> p,q,r = smt.Bools("p q r")
    >>> propagate([p, q, r, smt.And(p,q)], p & q)
    [p, q, And(p, q)]
    """
    # keyword param to also infer which are false?
    s = smt.Solver()
    s.add(known)
    maybes = list(maybes)
    while True:
        res = s.check()
        if res == smt.unsat:
            return maybes
        assert res == smt.sat
        m = s.model()
        maybes = [e for e in maybes if smt.is_true(m.eval(e))]
        s.add(smt.Not(smt.And(maybes)))


def propagate_eqs(terms: list[smt.ExprRef], known: smt.BoolRef) -> list[smt.BoolRef]:
    """
    Given a list of terms, propagate equalities among them that are implied by known.
    >>> x,y,z = smt.Ints("x y z")
    >>> terms = [x, y, z, x + 1, y + 1]
    >>> known = smt.And(x == y, y == z)
    >>> propagate_eqs(terms, known)
    [y == x, z == x, z == y, y + 1 == x + 1]
    """
    ts = defaultdict(list)
    for t in terms:
        ts[t.sort()].append(t)
    eqs = [
        t1 == t2
        for terms in ts.values()
        for n, t1 in enumerate(terms)
        for t2 in terms[:n]
    ]
    return propagate(eqs, known)


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


def find_calls(decl: smt.FuncDeclRef, t: smt.ExprRef) -> list[smt.ExprRef]:
    """
    Find subterms that are calls of decl in t.

    >>> f = smt.Function("f", smt.IntSort(), smt.IntSort())
    >>> find_calls(f, f(f(4*f(3)) + 2))
    [f(f(4*f(3)) + 2), f(4*f(3)), f(3)]
    """
    todo = [t]
    res = []
    while todo:
        t = todo.pop()
        if smt.is_app(t):
            if t.decl() == decl:
                res.append(t)
            todo.extend(t.children())
        else:
            raise ValueError("Expected an application term")
    return res


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


def bysect(
    thm, by: list[kd.kernel.Proof] | dict[object, kd.kernel.Proof], **kwargs
) -> Sequence[tuple[object, kd.kernel.Proof]]:
    """
    Bisect the `by` list to find a minimal set of premises that prove `thm`. Presents the same interface as `prove`

    >>> x,y,z = smt.Ints("x y z")
    >>> by = [kd.prove(x + 1 > x), kd.axiom(x == y), kd.prove(y + 1 > y), kd.axiom(y == z)]
    >>> bysect(x == z, by=by)
    [(1, |= x == y), (3, |= y == z)]
    """
    if isinstance(by, list):
        by1 = list(enumerate(by))
    elif isinstance(by, dict):
        by1 = list(by.items())
    else:
        raise ValueError("by must be a list or dict")
    n = 2
    while len(by1) >= 2:
        subset_size = len(by1) // n
        for i in range(0, len(by1), subset_size):
            rest = by1[:i] + by1[i + subset_size :]
            try:
                kd.prove(thm, by=[b for _, b in rest], **kwargs)
                by1 = rest
                n = max(n - 1, 2)
                break
            except Exception as _:
                pass
        else:
            if n == len(by1):
                break
            n = min(len(by1), n * 2)
    return by1


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


def consts(t: smt.ExprRef) -> set[smt.ExprRef]:
    """
    Return all constants in a term.

    >>> x,y = smt.Ints("x y")
    >>> consts(x + (y * y) + 1) == {smt.IntVal(1), x, y}
    True
    """
    ts = set()
    todo = [t]
    while todo:
        t = todo.pop()
        if smt.is_const(t):
            ts.add(t)
        elif smt.is_app(t):
            todo.extend(t.children())
        elif isinstance(t, smt.QuantifierRef):
            todo.append(t.body())
        elif smt.is_var(t):
            continue
        else:
            raise Exception("Unexpected term in consts", t)
    return ts


def decls(t: smt.ExprRef) -> set[smt.FuncDeclRef]:
    """Return all function declarations in a term."""
    return {e.decl() for e in subterms(t, into_binder=True) if smt.is_app(e)}


def defined_decls(t: smt.ExprRef) -> list[smt.FuncDeclRef]:
    """

    >>> x,y = smt.Ints("x y")
    >>> f = kd.define("test_f", [x,y], x + y)
    >>> g = smt.Function("g", smt.IntSort(), smt.IntSort())
    >>> defined_decls(f(x,y) + g(1))
    [test_f]
    """
    return [decl for decl in decls(t) if decl in kd.kernel.defns]


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


@dataclass(frozen=True)
class QuantifierHole:
    vs: list[smt.ExprRef]
    orig_vs: list[smt.ExprRef]  # to be able to exactly reconstruct original term?

    def has_right(self) -> bool:
        return False


class LambdaHole(QuantifierHole):
    def wrap(self, body: smt.ExprRef) -> smt.ExprRef:
        body = smt.substitute(body, *zip(self.vs, self.orig_vs))
        return smt.Lambda(self.orig_vs, body)


class ForAllHole(QuantifierHole):
    def wrap(self, body: smt.ExprRef) -> smt.ExprRef:
        body = smt.substitute(body, *zip(self.vs, self.orig_vs))
        return smt.ForAll(self.orig_vs, body)


class ExistsHole(QuantifierHole):
    def wrap(self, body: smt.ExprRef) -> smt.ExprRef:
        body = smt.substitute(body, *zip(self.vs, self.orig_vs))
        return smt.Exists(self.orig_vs, body)


@dataclass(frozen=True)
class DeclHole:
    f: smt.FuncDeclRef
    _left: tuple[smt.ExprRef, ...]
    _right: tuple[smt.ExprRef, ...]

    def wrap(self, e: smt.ExprRef) -> smt.ExprRef:
        return self.f(*self._left, e, *self._right)

    def left(self, t: smt.ExprRef) -> tuple["DeclHole", smt.ExprRef]:
        assert len(self._left) > 0
        return DeclHole(self.f, self._left[:-1], (t,) + self._right), self._left[-1]

    def right(self, t: smt.ExprRef) -> tuple["DeclHole", smt.ExprRef]:
        assert len(self._right) > 0
        return DeclHole(self.f, self._left + (t,), self._right[1:]), self._right[0]

    def has_left(self) -> bool:
        return len(self._left) > 0

    def has_right(self) -> bool:
        return len(self._right) > 0


type Hole = ForAllHole | ExistsHole | LambdaHole | DeclHole


@dataclass
class Zipper:
    """
    A zipper for traversing and modifying terms. The Zipper retains a context stack of "holes" and the current term.
    https://en.wikipedia.org/wiki/Zipper_(data_structure)

    >>> x,y,z = smt.Ints("x y z")
    >>> t = smt.Lambda([x,y], (x + y) * (y + z))
    >>> z1 = Zipper.from_term(t)
    >>> z1.open_binder().arg(1).left().arg(0)
    Zipper(ctx=[LambdaHole(vs=[X!..., Y!...], orig_vs=[x, y]), DeclHole(f=*, _left=(), _right=(Y!... + z,)), DeclHole(f=+, _left=(), _right=(Y!...,))], t=X!...)
    >>> z1.up().up().up()
    Zipper(ctx=[], t=Lambda([x, y], (x + y)*(y + z)))
    """

    ctx: list[Hole]  # trail / stack,. Consider saving old term
    t: smt.ExprRef

    @classmethod
    def from_term(cls, t: smt.ExprRef) -> "Zipper":
        return cls([], t)

    def up(self) -> "Zipper":  # up?
        hole = self.ctx.pop()
        self.t = hole.wrap(self.t)
        return self

    def rebuild(self) -> smt.ExprRef:
        while self.ctx:
            self.up()
        return self.t

    def copy(self) -> "Zipper":
        return Zipper(self.ctx.copy(), self.t)

    def left(self) -> "Zipper":
        hole = self.ctx.pop()
        assert isinstance(hole, DeclHole)
        hole, self.t = hole.left(self.t)
        self.ctx.append(hole)
        return self

    def right(self) -> "Zipper":
        hole = self.ctx.pop()
        assert isinstance(hole, DeclHole)
        hole, self.t = hole.right(self.t)
        self.ctx.append(hole)
        return self

    def arg(self, n: int) -> "Zipper":
        children = self.t.children()
        self.ctx.append(
            DeclHole(self.t.decl(), tuple(children[:n]), tuple(children[n + 1 :]))
        )
        self.t = children[n]
        return self

    def open_binder(self) -> "Zipper":
        assert isinstance(self.t, smt.QuantifierRef)
        t = self.t
        orig_vs, _body = kd.utils.open_binder_unhygienic(
            t
        )  # TODO: don't need to build body
        vs, body = kd.utils.open_binder(self.t)
        if self.t.is_forall():
            hole = ForAllHole(vs, orig_vs)
        elif self.t.is_exists():
            hole = ExistsHole(vs, orig_vs)
        elif self.t.is_lambda():
            hole = LambdaHole(vs, orig_vs)
        else:
            raise NotImplementedError("Unknown quantifier type", self.t)
        self.ctx.append(hole)
        self.t = body
        return self

    def __iter__(self):
        return self

    def __next__(self) -> smt.ExprRef:
        """
        All subterms of the term in a pre-order traversal.

        >>> x,y,z = smt.Ints("x y z")
        >>> list(Zipper([], x + y*z))
        [x, y*z, y, z]
        """
        if isinstance(self.t, smt.QuantifierRef):
            self.open_binder()
            return self.t
        elif smt.is_const(self.t):
            while len(self.ctx) != 0 and not self.ctx[-1].has_right():
                self.up()
            if len(self.ctx) == 0:
                raise StopIteration
            else:
                self.right()
                return self.t
        elif smt.is_app(self.t):
            self.arg(0)
            return self.t
        else:
            raise ValueError("Unexpected term in Zipper iteration", self.t)

    def pmatch(
        self, vs: list[smt.ExprRef], pat: smt.ExprRef
    ) -> Optional[dict[smt.ExprRef, smt.ExprRef]]:
        """
        Pattern match the current term against a pattern with variables vs.
        Leaves the zipper in a context state.
        This can be used to replace but rebuild using original context

        >>> x,y,z,a,b,c = smt.Ints("x y z a b c")
        >>> zip = Zipper([], x + smt.Lambda([y], y*z)[x])
        >>> (subst := zip.pmatch([a,b], a*b))
        {b: z, a: Y!...}
        >>> zip.t = smt.IntVal(1) * subst[a]
        >>> zip.rebuild()
        x + Lambda(y, 1*y)[x]
        """
        subst = pmatch(vs, pat, self.t)
        if subst is not None:
            return subst
        for t in self:
            subst = pmatch(vs, pat, t)
            if subst is not None:
                return subst

    def __hash__(self):
        """
        Warning: If you are hashing Zippers, make sure you are copying them.
        """
        return hash((tuple(self.ctx), self.t))


class ExprCtx(list):
    """
    A context of holes for an expression. Similar to Zipper, but with a nonmutating api
    """

    def copy(self) -> "ExprCtx":
        return ExprCtx(self[:])

    def arg(self, t: smt.ExprRef, n: int) -> tuple["ExprCtx", smt.ExprRef]:
        """
        >>> x,y,z = smt.Ints("x y z")
        >>> t = (x + y) * (y + z)
        >>> ExprCtx().arg(t, 1)
        ([DeclHole(f=*, _left=(x + y,), _right=())], y + z)
        """
        ctx = self.copy()
        children = t.children()
        ctx.append(DeclHole(t.decl(), tuple(children[:n]), tuple(children[n + 1 :])))
        return ctx, children[n]

    def wrap(self, t) -> smt.ExprRef:
        """
        Wrap a term t in the context
        >>> x,y,z = smt.Ints("x y z")
        >>> t = (x + y) * (y + z)
        >>> ctx, t1 = ExprCtx().arg(t, 1)
        >>> ctx.wrap(t1)
        (x + y)*(y + z)
        """
        for hole in reversed(self):
            t = hole.wrap(t)
        return t

    def children(self, t) -> list[tuple["ExprCtx", smt.ExprRef]]:
        """
        >>> x,y,z = smt.Ints("x y z")
        >>> t = (x + y) * (y + z)
        >>> ExprCtx().children(t)
        [([DeclHole(f=*, _left=(), _right=(y + z,))], x + y), ([DeclHole(f=*, _left=(x + y,), _right=())], y + z)]
        """
        children = t.children()
        res = []
        decl = t.decl()
        for n in range(len(children)):
            ctx = self.copy()
            ctx.append(DeclHole(decl, tuple(children[:n]), tuple(children[n + 1 :])))
            res.append((ctx, children[n]))
        return res

    def open_binder(self, t: smt.QuantifierRef) -> tuple["ExprCtx", smt.ExprRef]:
        """
        >>> x,y = smt.Ints("x y")
        >>> t = smt.Lambda([x], x + y)
        >>> ExprCtx().open_binder(t)
        ([LambdaHole(vs=[X!...], orig_vs=[x])], X!... + y)
        """
        assert isinstance(t, smt.QuantifierRef)
        ctx = self.copy()
        orig_vs, _body = kd.utils.open_binder_unhygienic(
            t
        )  # TODO: don't need to build body
        vs, body = kd.utils.open_binder(t)
        if t.is_forall():
            hole = ForAllHole(vs, orig_vs)
        elif t.is_exists():
            hole = ExistsHole(vs, orig_vs)
        elif t.is_lambda():
            hole = LambdaHole(vs, orig_vs)
        else:
            raise NotImplementedError("Unknown quantifier type", t)
        ctx.append(hole)
        return ctx, body


def pmatch_rec_ctx(
    vs: list[smt.ExprRef], pat: smt.ExprRef, t: smt.ExprRef
) -> Optional[tuple[ExprCtx, smt.ExprRef, dict[smt.ExprRef, smt.ExprRef]]]:
    """
    Pattern match `pat` against subterms of `t`, returning the context, matched term, and substitution if successful.
    >>> x,y,z,a,b = smt.Ints("x y z a b")
    >>> kd.utils.pmatch_rec_ctx([a,b], a*b, smt.Lambda([x], x * y))
    ([LambdaHole(vs=[X!...], orig_vs=[x])], X!...*y, {b: y, a: X!...})
    """
    todo = [(ExprCtx(), t)]
    while todo:
        ctx, t = todo.pop()
        subst = pmatch(vs, pat, t)
        if subst is not None:
            return ctx, t, subst
        elif smt.is_app(t):
            todo.extend(ctx.children(t))
        elif isinstance(t, smt.QuantifierRef):
            todo.append(ctx.open_binder(t))
        else:
            raise ValueError("Unexpected term in pmatch_rec_ctx", t)


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
    {('thm1', |= ForAll(x, x + 0 == x)): [z], ('thm2', |= z + 0 == z): []}
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
