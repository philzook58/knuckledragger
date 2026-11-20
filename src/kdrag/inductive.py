"""Relation operators and intersections of closed predicates."""

from __future__ import annotations

import kdrag as kd
from kdrag import smt


def relation_operator(
    f: smt.FuncDeclRef,
    args: smt.ExprRef | list[smt.ExprRef],
    *clauses: smt.BoolRef,
) -> smt.QuantifierRef:
    """Abstract calls to ``f`` into an SMT relation-to-relation lambda.

    ``F(R)(*args)`` substitutes directly into both lambdas. No monotonicity or
    fixed-point property is assumed or proved.
    """
    if isinstance(args, smt.ExprRef):
        args = [args]
    sorts = [x.sort() for x in args]
    R = smt.FreshConst(smt.ArraySort(*sorts, smt.BoolSort()), prefix="R")
    replacement = R(*[smt.Var(i, sort) for i, sort in enumerate(sorts)])
    body_R = smt.substitute_funs(smt.Or(*clauses), (f, replacement))
    return smt.Lambda(R, smt.Lambda(args, body_R))


def define_least(
    f: smt.FuncDeclRef,
    args: smt.ExprRef | list[smt.ExprRef],
    *clauses: smt.BoolRef,
) -> smt.FuncDeclRef:
    """Define the intersection of all predicates closed under the clauses.

    This intersection is defined even for nonmonotone operators, but need not
    itself be closed. Only the ordinary quantified ``defn`` is registered.
    """
    if isinstance(args, smt.ExprRef):
        args = [args]
    F = relation_operator(f, args, *clauses)
    R = smt.FreshConst(F.sort().domain(), prefix="R")
    return kd.define(
        f.name(),
        args,
        smt.ForAll(R, smt.ForAll(args, F(R)(*args), R(*args)), R(*args)),
    )


def _least(F: smt.FuncRef):
    relation = F.sort().domain()
    args = [smt.FreshConst(s, prefix="x") for s in smt.domains(relation)]
    R = smt.FreshConst(relation, prefix="R")
    Z = smt.Lambda(
        args, smt.ForAll(R, smt.ForAll(args, F(R)(*args), R(*args)), R(*args))
    )
    return args, Z


def _normal(term: smt.BoolRef) -> smt.BoolRef:
    from kdrag.rewrite import beta

    while True:
        result = beta(term)
        if result.eq(term):
            return term
        assert isinstance(result, smt.BoolRef)
        term = result


def _subset(args, A, B):
    return _normal(smt.ForAll(args, A(*args), B(*args)))


def _least_induct(F, args, Z):
    R = smt.FreshConst(F.sort().domain(), prefix="R")
    # forall R. (F(R) <= R) -> (Z <= R), where Z is the intersection.
    pf = kd.Lemma(smt.ForAll(R, _subset(args, F(R), R), _subset(args, Z, R)))
    R = pf.fix()
    pf.intro()
    pf.fixes()
    member = pf.intro()
    pf.specialize(member, R)
    pf.auto()
    return pf.qed()


def least_induct(F: smt.FuncRef) -> kd.Proof:
    """Derive leastness for the relation operator F, without monotonicity."""
    # forall R. (F(R) <= R) -> (Z <= R), Z = intersection of closed predicates.
    args, Z = _least(F)
    return _least_induct(F, args, Z)


def least_unfold(F: smt.FuncRef) -> kd.Proof:
    """Derive unfolding of the intersection, conditional on monotonicity of F."""
    args, Z = _least(F)
    R, S = [smt.FreshConst(F.sort().domain(), prefix=p) for p in ("R", "S")]
    mono = smt.ForAll([R, S], _subset(args, R, S), _subset(args, F(R), F(S)))
    least = _least_induct(F, args, Z)
    # mono(F) -> forall args. Z(args) == F(Z)(args).
    pf = kd.Lemma(
        smt.Implies(mono, _normal(smt.ForAll(args, smt.Eq(Z(*args), F(Z)(*args)))))
    )
    monotone = pf.intro()

    def specialize(state, rule, *terms):
        h = state.specialize(rule, *terms, keep=True)
        normal = _normal(h)
        if not normal.eq(h):
            eq = kd.kernel.prove(
                smt.Eq(h, normal), solver=lambda: smt.Then("simplify", "smt").solver()
            )
            state.rw(eq, at=h)
            h = state.top_goal().ctx[-1]
        return h

    # First establish F(Z) <= Z, using Z <= every closed candidate R.
    closure_goal = _subset(args, F(Z), Z)
    pf.have(closure_goal)
    with pf.sub() as sub:
        points = sub.fixes()
        sub.intro()
        candidate = sub.fix()
        closed = sub.intro()
        bound = sub.specialize(least, candidate, closed)
        mapped = specialize(sub, monotone, Z, candidate)
        sub.specialize(mapped, bound, *points)
        sub.specialize(closed, *points)
        sub.auto()
    closed = closure_goal
    mapped = specialize(pf, monotone, F(Z), Z)
    # F(Z) is closed: monotonicity turns F(Z) <= Z into F(F(Z)) <= F(Z).
    fg_closed = pf.specialize(mapped, closed)
    # Leastness with candidate F(Z) then gives Z <= F(Z).
    back_rule = specialize(pf, least, F(Z))
    back = pf.specialize(back_rule, fg_closed)
    points = pf.fixes()
    forward_point = pf.specialize(closed, *points)
    back_point = pf.specialize(back, *points)
    a, b = smt.Bools("a b")
    antisym = kd.prove(
        smt.ForAll([a, b], smt.Implies(a, b), smt.Implies(b, a), smt.Eq(a, b))
    )
    pf.specialize(
        antisym, _normal(Z(*points)), _normal(F(Z)(*points)), back_point, forward_point
    )
    pf.auto()
    return pf.qed()
