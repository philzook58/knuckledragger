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


def _subset(args, A, B):
    return smt.ForAll(args, A(*args), B(*args))


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
    pf = kd.Lemma(smt.Implies(mono, smt.ForAll(args, smt.Eq(Z(*args), F(Z)(*args)))))
    monotone = pf.intro()

    # F(Z) <= Z: every closed candidate contains Z and hence F(Z).
    closed = pf.have(_subset(args, F(Z), Z))
    with pf.sub() as sub:
        points = sub.fixes()
        sub.intro()
        candidate = sub.fix()
        closure = sub.intro()
        sub.specialize(least, candidate, closure)
        sub.specialize(monotone, Z, candidate, keep=True)
        mapped = sub.have(_subset(args, F(Z), F(candidate)), by=[])
        sub.specialize(mapped, *points)
        sub.specialize(closure, *points)
        sub.auto()

    # F(F(Z)) <= F(Z), so leastness with candidate F(Z) gives Z <= F(Z).
    pf.specialize(monotone, F(Z), Z, keep=True)
    pf.have(_subset(args, F(F(Z)), F(Z)), by=[])
    pf.specialize(least, F(Z))
    back = pf.have(_subset(args, Z, F(Z)), by=[])
    points = pf.fixes()
    forward = pf.specialize(closed, *points)
    backward = pf.specialize(back, *points)
    # Direct equality search still times out for existential clauses.
    # Instantiate propositional antisymmetry to close this final step.
    a, b = smt.Bools("a b")
    antisym = kd.prove(
        smt.ForAll([a, b], smt.Implies(a, b), smt.Implies(b, a), smt.Eq(a, b))
    )
    pf.specialize(antisym, Z(*points), F(Z)(*points), backward, forward)
    pf.assumption()
    return pf.qed()
