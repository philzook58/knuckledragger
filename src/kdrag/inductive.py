"""Inductive predicates as least closed relations, without evidence datatypes."""

from __future__ import annotations

from typing import Sequence, TypeVar, cast

import kdrag as kd
from kdrag import smt
from kdrag.rewrite import beta as beta_step


T = TypeVar("T", bound=smt.ExprRef)


def _beta(term: T) -> T:
    """Normalize nested lambda selections exposed by earlier reductions."""
    while True:
        result = beta_step(term)
        if result.eq(term):
            return cast(T, result)
        term = cast(T, result)


def indrel(
    name: str,
    args: smt.ExprRef | list[smt.ExprRef],
    *clauses: smt.BoolRef,
    mono_by: Sequence[kd.Proof] = (),
) -> smt.FuncDeclRef:
    """Define the least relation closed under ``clauses``.

    Declare a Boolean function with the same name and signature to refer to it
    recursively in clauses. Monotonicity must be provable using ``mono_by``.
    The returned function has ``case0``, ... introduction proofs, an ``induct``
    theorem quantified over predicate arrays, and a proved unfolding ``defn``.
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
    R, S = [smt.FreshConst(relation, prefix=p) for p in ("R", "S")]
    replacement = smt.Select(R, *[smt.Var(i, s) for i, s in enumerate(sorts)])
    body = smt.Or(*clauses)
    abstract = smt.substitute_funs(body, (f, replacement))
    if kd.kernel.decl_occurs(f, abstract):
        raise ValueError("Could not abstract all recursive occurrences", f)

    def operator(A):
        return smt.Lambda(args, smt.substitute(abstract, (R, A)))

    def subset(A, B):
        return _beta(smt.ForAll(args, smt.Select(A, *args), smt.Select(B, *args)))

    obligation = smt.ForAll([R, S], subset(R, S), subset(operator(R), operator(S)))
    try:
        mono = kd.prove(obligation, by=mono_by)
    except (kd.kernel.LemmaError, TimeoutError) as exc:
        raise ValueError("Could not establish monotonicity", obligation) from exc

    # Intersection of closed predicates. No recursive equation is assumed.
    G = smt.Lambda(args, smt.ForAll(R, subset(operator(R), R), smt.Select(R, *args)))
    pf = kd.Lemma(smt.ForAll(R, subset(operator(R), R), subset(G, R)))
    pred = pf.fix()
    pf.intro()
    points = pf.fixes()
    membership = pf.intro()
    pf.specialize(membership, pred)
    pf.auto()
    least = pf.qed()

    pf = kd.Lemma(subset(operator(G), G))
    points = pf.fixes()
    pf.intro()
    pred = pf.fix()
    closure = pf.intro()
    bound = pf.specialize(least, pred, closure)
    instance = mono(G, pred)
    instance = kd.prove(_beta(instance.thm), by=[instance])
    pf.specialize(instance, bound, *points)
    pf.specialize(closure, *points)
    pf.auto()
    closed = pf.qed()

    def reduced(p):
        return kd.prove(_beta(p.thm), by=[p])

    fg_closed = kd.kernel.modus(reduced(mono(operator(G), G)), closed)
    back = kd.kernel.modus(reduced(least(operator(G))), fg_closed)
    a, b = smt.Bools("indrel_a indrel_b")
    antisym = kd.prove(
        smt.ForAll([a, b], smt.Implies(a, b), smt.Implies(b, a), smt.Eq(a, b))
    )
    pf = kd.Lemma(
        _beta(
            smt.ForAll(
                args, smt.Eq(smt.Select(G, *args), smt.Select(operator(G), *args))
            )
        )
    )
    points = pf.fixes()
    left = _beta(smt.Select(G, *points))
    right = _beta(smt.Select(operator(G), *points))
    pf.exact(antisym(left, right, back(*points), closed(*points)))
    unfolding = pf.qed()

    # Register only after all fixed-point obligations have succeeded.
    f = kd.define(name, args, _beta(smt.Select(G, *args)))
    pf = kd.Lemma(smt.ForAll(args, smt.Eq(f(*args), body)))
    points = pf.fixes()
    pf.unfold(f)
    pf.exact(reduced(unfolding(*points)))
    equation = pf.qed()

    conditions = []
    for i, clause in enumerate(clauses):
        variables = list(args)
        premise = clause
        while isinstance(premise, smt.QuantifierRef) and premise.is_exists():
            witnesses, premise = kd.kernel.open_binder(premise)
            variables.extend(witnesses)
        rule = kd.prove(smt.ForAll(variables, premise, f(*args)), by=[equation])
        setattr(f, f"case{i}", rule)
        replaced = smt.substitute_funs(clause, (f, replacement))
        conditions.append(smt.ForAll(args, replaced, smt.Select(R, *args)))
    pf = kd.Lemma(
        smt.ForAll(
            R, smt.And(*conditions), smt.ForAll(args, f(*args), smt.Select(R, *args))
        )
    )
    pred = pf.fix()
    pf.intro()
    points = pf.fixes()
    membership = pf.intro()
    pf.unfold(f, at=membership)
    membership = pf.top_goal().ctx[-1]
    pf.specialize(membership, pred)
    pf.auto()
    setattr(f, "induct", pf.qed())
    kd.kernel.register_definition(kd.kernel.make_unfolding(equation))
    return f
