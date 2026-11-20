"""Relation operators and intersections of closed predicates."""

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
