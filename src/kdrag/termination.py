"""
Do not use. Work in progress

"""

import kdrag.smt as smt
import kdrag as kd
import itertools

"""
Maybe have size as axiom schema in kernel and make a tactic that instantiates it's definitions.
Looking somewhat similar to refinement subsystem then
"""


def opaque_abs_size(e: smt.ExprRef) -> smt.ExprRef:
    """A kludge to get around the fact that Z3's size function can return negative values, which breaks some of my proofs."""
    return smt.Abs(smt.Function(e.sort().name() + ".size", e.sort(), smt.IntSort())(e))


def default_measure(e: smt.ExprRef) -> smt.ExprRef:
    """
    Some default measures for built in types and algebraic datatypes.

    >>> x = smt.Int("x")
    >>> kd.prove(default_measure(smt.IntVal(5)) == 5)
    |= If(5 > 0, 5, -5) == 5
    >>> assert default_measure(kd.Nat.S(kd.Nat.Z)) == 2
    >>> kd.prove(default_measure(kd.seq(1,2,3)) == 3)
    |= Length(Concat(Unit(1), Concat(Unit(2), Unit(3)))) == 3
    >>> _ = kd.prove(default_measure(kd.Nat.S(kd.Nat.Z).pred) == 1)
    >>> x = smt.Const("x", kd.Nat)
    >>> _ = kd.prove(smt.Implies(x.is_S, default_measure(x) > default_measure(x.pred)))
    >>> _ = kd.prove(smt.Implies(smt.And(x.is_S, x.pred.is_S), default_measure(x) > default_measure(x.pred.pred)))
    >>> y = smt.BitVec("y",32)
    >>> kd.prove(default_measure(smt.BitVecVal(-1, 32)) > default_measure(smt.BitVecVal(0, 32)))
    |= BV2Int(4294967295) > BV2Int(0)

    """
    # Should I emit an expression + side conditions
    if isinstance(e, smt.DatatypeRef):
        if smt.is_constructor(e):
            # Max?
            return 1 + smt.Sum(default_measure(arg) for arg in e.children())
        elif smt.is_accessor(e):
            # secondly it's inconsistent with the sum definition
            acc = e.decl()
            x = e.arg(0)
            sort = x.sort()
            # i,j = kd.utils.find_accessor(acc)
            for i in range(sort.num_constructors()):
                constr = sort.constructor(i)
                for j in range(constr.arity()):
                    if acc == sort.accessor(i, j):
                        return smt.If(
                            sort.recognizer(i)(x),
                            default_measure(
                                e.arg(0)
                            )  # The reverse of the above constructor calculation
                            - 1
                            - smt.Sum(
                                [
                                    # smt.Abs(smt.FreshInt())
                                    # Can't actually recurse. sort.size(accessor)
                                    opaque_abs_size(sort.accessor(i, k)(x))
                                    for k in range(constr.arity())
                                    if k != j
                                ]
                            ),
                            smt.FreshInt(),  # unspecified if the recognizer doesn't hold. Could make it abs?
                        )
            else:
                raise NotImplementedError(
                    f"Could not find accessor {acc} in sort {sort}. Something has gone wrong."
                )
        else:
            sort = e.sort()
            # + size >= 0, but abs does that... Hmm.
            # Abs is kind of a kludge.
            # abs(size(t)) = size(t) since size >= 0
            return opaque_abs_size(e)
    elif isinstance(e, smt.SeqRef):
        return smt.Length(
            e
        )  # TODO:, could recurse? Just recurse on first arg if nonempty? Rather than full Fold definition so we don't have to internalize
        # Or first N bounded args
    elif isinstance(e, smt.BitVecRef):
        return smt.BV2Int(e, is_signed=False)
    # TODO: some other possible default measurable objects
    # Finset => Card
    # Array over finsort -> lex
    # Reals are interesting (continuous recursion / induction) but for now reject.
    sort = e.sort()
    if sort == smt.IntSort():
        return smt.Abs(e)
    else:
        raise NotImplementedError(f"No default measure for {e} of sort {sort}")


def lex_gt(
    es: list[smt.ExprRef],
    es1: list[smt.ExprRef],
    measure=default_measure,
) -> smt.BoolRef:
    """
    Lexicographic greater than on lists of expressions.

    >>> x, y = smt.Consts("x y", kd.Nat)
    >>> _ = kd.prove(smt.Implies(x.is_S, lex_gt([x], [x.pred])))
    >>> _ = kd.prove(smt.Implies(y.is_S, lex_gt([x, y], [x, y.pred])))
    >>> _ = kd.prove(smt.Implies(y.is_S, smt.Not(lex_gt([x, y.pred], [x, y]))))
    >>> _ = kd.prove(smt.Not(lex_gt([x, y], [x, y])))
    >>> _ = kd.prove(smt.Implies(x.is_S, lex_gt([x, y], [x.pred, y])))
    """
    # _ = kd.prove(lex_gt([3,4,5], [3,4,4])). What should I do with constants
    assert len(es) == len(es1) and len(es) > 0
    me, me1 = measure(es[0]), measure(es1[0])
    if len(es) == 1:
        return me > me1
    else:
        return smt.Or(
            me > me1,
            smt.And(me == me1, lex_gt(es[1:], es1[1:])),
        )


def search_wf(
    head: list[smt.ExprRef],
    calls: list[tuple[smt.BoolRef, list[smt.ExprRef]]],
    measure=default_measure,
) -> tuple[int, ...]:
    """
    Find a permutation that makes every head greater than every call.

    >>> x, y = smt.Consts("x y", kd.Nat)
    >>> search_wf([x, y], [(x.is_S, [x.pred, y])])
    (0, 1)
    >>> search_wf([x, y], [(y.is_S, [x, y.pred])])
    (0, 1)
    >>> search_wf([x, y], [(y.is_S, [kd.Nat.S(x), y.pred])])
    (1, 0)
    """
    assert all(len(e[1]) == len(head) for e in calls)
    for perm in itertools.permutations(range(len(head))):
        phead = [head[i] for i in perm]
        pes1 = [(ctx, [e[i] for i in perm]) for ctx, e in calls]
        try:
            _ = kd.prove(
                smt.And(
                    [
                        smt.Implies(ctx, lex_gt(phead, e1, measure=measure))
                        for ctx, e1 in pes1
                    ]
                )
            )
            return perm
        except kd.kernel.LemmaError:
            pass
    raise ValueError("No well founded ordering found", head, ">", calls)
