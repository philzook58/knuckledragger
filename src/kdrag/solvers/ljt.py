"""
Dyckhoff Intuitionistic Propositional Prover

- https://www.cs.cmu.edu/~fp/courses/15317-f08/cmuonly/dyckhoff92.pdf
- https://www.philipzucker.com/ljt/


"""

import kdrag.smt as smt


def prove(goal: smt.BoolRef) -> tuple[bool, list]:
    """
    Prove goal intuitionistically using Dyckhoff's LJT calculus.

    >>> a,b,c,d = smt.Bools('a b c d')
    >>> Not, Or, Implies, And = smt.Not, smt.Or, smt.Implies, smt.And
    >>> prove(smt.Not(a))[0]
    False
    >>> prove(a)[0]
    False
    >>> prove(smt.Implies(a, a))[0]
    True
    >>> prove(smt.Or(a, smt.Not(a)))[0] # excluded middle
    False
    >>> prove(smt.Not(Not(Or(a, Not(a)))))[0]
    True
    >>> prove(smt.Implies(a, Implies(b, a)))[0]
    True
    >>> prove(smt.Implies(And(a, b), And(b, a)))[0]
    True
    >>> prove(smt.Implies(And(a, b), a))[0]
    True
    >>> prove(smt.Implies(Implies(Implies(a, b), a), a))[0] # pierce's law
    False
    >>> prove(smt.Not(Not(Implies(Implies(Implies(a, b), a), a))))[0]
    True
    """
    trace = []

    def right_inv(ctx, invctx, goal):
        # print("right",ctx, invctx, goal)
        trace.append(("right", ctx, invctx, goal))
        if smt.is_true(goal):  # R true
            return True
        elif smt.is_and(goal):  # R and
            return all(right_inv(ctx, invctx, subgoal) for subgoal in goal.children())
        elif smt.is_implies(goal):  # R impl
            return right_inv(ctx, invctx + [goal.arg(0)], goal.arg(1))
        elif smt.is_not(goal):  # treat not as `a -> False``
            return right_inv(ctx, invctx, smt.Implies(goal.arg(0), smt.BoolVal(False)))
        elif (
            smt.is_false(goal) or smt.is_or(goal) or smt.is_const(goal)
        ):  # not right invertible
            return left_inv(ctx, invctx, goal)
        else:
            raise Exception(f"Unexpected formula in right_inv {goal}")

    def left_inv(ctx, invctx, goal):
        # print("left", ctx, invctx, goal)
        trace.append(("left", ctx, invctx, goal))
        if len(invctx) == 0:
            return search(ctx, goal)
        c = invctx[-1]
        invctx = invctx[:-1]
        if smt.is_false(c):
            return True
        elif smt.is_and(c):  # L and
            return left_inv(ctx, invctx + c.children(), goal)
        elif smt.is_or(c):  # L or
            return all(left_inv(ctx, invctx + [c], goal) for c in c.children())
        elif smt.is_implies(c):  # Some specializations of L impl
            hyp, conc = c.children()
            if smt.is_false(hyp):
                return left_inv(ctx, invctx, goal)
            elif smt.is_true(hyp):
                return left_inv(ctx, invctx + [conc], goal)
            elif smt.is_and(hyp):
                # curry all
                for x in hyp.children():
                    conc = smt.Implies(x, conc)
                return left_inv(ctx, invctx + [conc], goal)
            elif smt.is_or(hyp):
                return left_inv(
                    ctx, invctx + [smt.Implies(c, conc) for c in hyp.children()], goal
                )
            elif smt.is_implies(hyp) or smt.is_const(hyp) or smt.is_not(hyp):
                return left_inv(ctx + [c], invctx, goal)
            else:
                raise Exception(f"Unexpected implication in left_inv {c}")
        elif smt.is_const(c):
            return left_inv(ctx + [c], invctx, goal)
        elif smt.is_not(c):  # Turn not into intuitinistic c.arg(0) -> bottom
            return left_inv(
                ctx, invctx + [smt.Implies(c.arg(0), smt.BoolVal(False))], goal
            )
        else:
            raise Exception(f"Unexpected formula in left_inv {c}")

    def search(ctx, goal):
        # print("search", ctx, goal)
        trace.append(("search", ctx, goal))
        if any(c.eq(goal) for c in ctx):  # a slightly extened prop rule. is_const()
            return True
        if smt.is_or(goal):
            if any(right_inv(ctx, [], c) for c in goal.children()):
                return True
        for i, c in enumerate(ctx):
            if smt.is_implies(c):
                hyp, conc = c.children()
                if any(c.eq(hyp) for c in ctx):  # hmm. maybe this is ok. Left implprop
                    ctx1 = ctx[:i] + ctx[i + 1 :]
                    if left_inv(ctx1, [conc], goal):
                        return True
                if smt.is_not(hyp):
                    hyp = smt.Implies(hyp.arg(0), smt.BoolVal(False))
                if smt.is_implies(hyp):  # left impl impl
                    a, b = hyp.children()
                    ctx1 = ctx[:i] + ctx[i + 1 :]
                    return right_inv(ctx1, [smt.Implies(b, conc), a], b) and left_inv(
                        ctx1, [conc], goal
                    )
        return False

    return right_inv([], [], goal), trace
