"""Intersections of closed predicates and monotone inductive relations."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

import kdrag as kd
from kdrag import smt
from kdrag.rewrite import beta as beta_step


@dataclass
class _LeastDefinition:
    args: list[smt.ExprRef]
    body: smt.BoolRef
    operator: Callable
    subset: Callable
    G: Callable
    least: kd.Proof
    definition: kd.kernel.Unfolding


_least_definitions: dict[smt.FuncDeclRef, _LeastDefinition] = {}


def define_least(
    name: str, args: smt.ExprRef | list[smt.ExprRef], *clauses: smt.BoolRef
) -> smt.FuncDeclRef:
    """Define the intersection of predicates closed under the clauses.

    No monotonicity is required. ``f.induct`` expresses leastness; ``f.defn``
    unfolds the quantified intersection, which need not itself be closed.
    """
    if isinstance(args, smt.ExprRef):
        args = [args]
    if not args or any(not smt.is_const(a) or not smt.is_uninterp(a) for a in args):
        raise ValueError("indrel arguments must be nonempty distinct constants")
    if len({a.get_id() for a in args}) != len(args):
        raise ValueError("indrel arguments must be distinct")
    if any(not smt.is_bool(c) for c in clauses):
        raise TypeError("indrel clauses must be Boolean expressions")
    sorts = [a.sort() for a in args]
    f = smt.Function(name, *sorts, smt.BoolSort())
    if f in kd.kernel.defns:
        raise ValueError("Relation is already defined", f)
    relation = smt.ArraySort(*sorts, smt.BoolSort())
    R = smt.FreshConst(relation, prefix="R")
    body = smt.Or(*clauses)

    def array_predicate(A):
        return lambda *xs: smt.Select(A, *xs)

    def operator(P):
        replacement = smt.substitute(
            P(*args), *[(a, smt.Var(i, a.sort())) for i, a in enumerate(args)]
        )
        term = smt.substitute_funs(body, (f, replacement))
        if kd.kernel.decl_occurs(f, term):
            raise ValueError("Could not abstract all recursive occurrences", f)
        return lambda *xs: smt.substitute(term, *zip(args, xs))

    def subset(P, Q):
        return smt.ForAll(args, P(*args), Q(*args))

    r = array_predicate(R)
    # Intersection of closed predicates. No recursive equation is assumed.
    g_body = smt.ForAll(R, subset(operator(r), r), r(*args))

    def G(*xs):
        return smt.substitute(g_body, *zip(args, xs))

    pf = kd.Lemma(smt.ForAll(R, subset(operator(r), r), subset(G, r)))
    pred = pf.fix()
    pf.intro()
    pf.fixes()
    membership = pf.intro()
    pf.specialize(membership, pred)
    pf.auto()
    least = pf.qed()

    f = kd.define(name, args, G(*args))
    definition = kd.kernel.defns[f]
    pf = kd.Lemma(smt.ForAll(R, subset(operator(r), r), subset(f, r)))
    pred = pf.fix()
    pf.intro()
    pf.fixes()
    membership = pf.intro()
    pf.unfold(f, at=membership)
    membership = pf.top_goal().ctx[-1]
    pf.specialize(membership, pred)
    pf.auto()
    setattr(f, "induct", pf.qed())
    _least_definitions[f] = _LeastDefinition(
        args, body, operator, subset, G, least, definition
    )
    return f


def prove_monotone(f: smt.FuncDeclRef, by: Sequence[kd.Proof] = ()) -> kd.Proof:
    """Prove monotonicity of a relation's clause operator; change no definitions."""
    info = _least_definitions[f]
    relation = smt.ArraySort(*[a.sort() for a in info.args], smt.BoolSort())
    R, S = [smt.FreshConst(relation, prefix=p) for p in ("R", "S")]

    def r(*xs):
        return smt.Select(R, *xs)

    def s(*xs):
        return smt.Select(S, *xs)

    operator, subset = info.operator, info.subset
    obligation = smt.ForAll([R, S], subset(r, s), subset(operator(r), operator(s)))
    try:
        return kd.prove(obligation, by=by)
    except (kd.kernel.LemmaError, TimeoutError) as exc:
        raise ValueError("Could not establish monotonicity", obligation) from exc


def prove_unfolding(f: smt.FuncDeclRef, mono: kd.Proof) -> kd.Proof:
    """Derive recursive unfolding without registering it or replacing ``f.defn``."""
    info = _least_definitions[f]
    args, body, operator, subset, G, least = (
        info.args,
        info.body,
        info.operator,
        info.subset,
        info.G,
        info.least,
    )
    G_array = smt.Lambda(args, G(*args))

    def reduced(p):
        # Only specialization of predicate arrays introduces SMT lambda selects.
        term = p.thm
        while True:
            result = beta_step(term)
            if result.eq(term):
                return kd.prove(term, by=[p])
            assert isinstance(result, smt.BoolRef)
            term = result

    pf = kd.Lemma(subset(operator(G), G))
    points = pf.fixes()
    pf.intro()
    pred = pf.fix()
    closure = pf.intro()
    bound = pf.specialize(least, pred, closure)
    instance = reduced(mono(G_array, pred))
    pf.specialize(instance, bound, *points)
    pf.specialize(closure, *points)
    pf.auto()
    closed = pf.qed()

    fg_closed = kd.kernel.modus(
        reduced(mono(smt.Lambda(args, operator(G)(*args)), G_array)), closed
    )
    back = kd.kernel.modus(
        reduced(least(smt.Lambda(args, operator(G)(*args)))), fg_closed
    )
    # Apply propositional antisymmetry directly; do not re-search inside G.
    a, b = smt.Bools("indrel_a indrel_b")
    antisym = kd.prove(
        smt.ForAll([a, b], smt.Implies(a, b), smt.Implies(b, a), smt.Eq(a, b))
    )
    pf = kd.Lemma(smt.ForAll(args, smt.Eq(G(*args), operator(G)(*args))))
    points = pf.fixes()
    pf.exact(antisym(G(*points), operator(G)(*points), back(*points), closed(*points)))
    unfolding = pf.qed()

    pf = kd.Lemma(smt.ForAll(args, smt.Eq(f(*args), body)))
    points = pf.fixes()
    _, trace = kd.kernel.unfold_defns(pf.top_goal().goal, [info.definition])
    pf.rw(trace)
    pf.exact(unfolding(*points))
    return pf.qed()


def indrel(
    name: str,
    args: smt.ExprRef | list[smt.ExprRef],
    *clauses: smt.BoolRef,
    mono_by: Sequence[kd.Proof] = (),
) -> smt.FuncDeclRef:
    """Define the intersection, prove monotonicity, and register recursive unfolding.

    If monotonicity fails, the valid intersection definition remains available
    for inspection or a later proof using ``prove_monotone``.
    """
    f = define_least(name, args, *clauses)
    mono = prove_monotone(f, by=mono_by)
    unfolding = prove_unfolding(f, mono)
    kd.kernel.register_definition(kd.kernel.make_unfolding(unfolding))
    return f
