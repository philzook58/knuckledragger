"""Inductive predicates as least closed relations, without evidence datatypes."""

from __future__ import annotations

from typing import Sequence

import kdrag as kd
from kdrag import smt
from kdrag.rewrite import beta as beta_step


def indrel(
    name: str,
    args: smt.ExprRef | list[smt.ExprRef],
    *clauses: smt.BoolRef,
    mono_by: Sequence[kd.Proof] = (),
) -> smt.FuncDeclRef:
    """Define the least relation closed under ``clauses``.

    Declare a Boolean function with the same name and signature to refer to it
    recursively in clauses. Monotonicity must be provable using ``mono_by``.
    The returned function has an ``induct`` theorem quantified over predicate
    arrays and a proved unfolding ``defn``.
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

    r, s = array_predicate(R), array_predicate(S)
    obligation = smt.ForAll([R, S], subset(r, s), subset(operator(r), operator(s)))
    try:
        mono = kd.prove(obligation, by=mono_by)
    except (kd.kernel.LemmaError, TimeoutError) as exc:
        raise ValueError("Could not establish monotonicity", obligation) from exc

    # Intersection of closed predicates. No recursive equation is assumed.
    g_body = smt.ForAll(R, subset(operator(r), r), r(*args))

    def G(*xs):
        return smt.substitute(g_body, *zip(args, xs))

    G_array = smt.Lambda(args, G(*args))
    pf = kd.Lemma(smt.ForAll(R, subset(operator(r), r), subset(G, r)))
    pred = pf.fix()
    pf.intro()
    points = pf.fixes()
    membership = pf.intro()
    pf.specialize(membership, pred)
    pf.auto()
    least = pf.qed()

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

    # Register only after all fixed-point obligations have succeeded.
    f = kd.define(name, args, G(*args))
    pf = kd.Lemma(smt.ForAll(args, smt.Eq(f(*args), body)))
    points = pf.fixes()
    pf.unfold(f)
    pf.exact(unfolding(*points))
    equation = pf.qed()

    pf = kd.Lemma(smt.ForAll(R, subset(operator(r), r), subset(f, r)))
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
