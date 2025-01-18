"""
Tactics are helpers that organize calls to the kernel. The code of these helpers don't have to be trusted.
"""

import kdrag as kd
import kdrag.smt as smt
from enum import IntEnum
import operator as op
from . import config
from typing import NamedTuple, Iterable, Optional, Sequence, Callable


class Calc:
    """
    Calc is for equational reasoning.
    One can write a sequence of formulas interspersed with useful lemmas.
    """

    class _Mode(IntEnum):
        EQ = 0
        LE = 1
        LT = 2
        GT = 3
        GE = 4

        def __str__(self):
            names = ["==", "<=", "<", ">", ">="]
            return names[self]

        @property
        def op(self):
            ops = [op.eq, op.le, op.lt, op.gt, op.ge]
            return ops[self]

        def trans(self, y):
            """Allowed transitions"""
            if self == y or self == self.EQ:
                return True
            else:
                if self == self.LE and y == self.LT or self == self.GE and y == self.GT:
                    return True
                else:
                    return False

    def __init__(self, vars: list[smt.ExprRef], lhs: smt.ExprRef, assume=[]):
        self.vars = vars
        self.lhs = lhs
        self.iterm = lhs  # intermediate term
        self.assume = assume
        self.lemma = kd.kernel.lemma(self._forall(smt.Eq(lhs, lhs)))
        self.mode = self._Mode.EQ

    def _forall(
        self, body: smt.BoolRef | smt.QuantifierRef
    ) -> smt.BoolRef | smt.QuantifierRef:
        if len(self.assume) == 1:
            body = smt.Implies(self.assume[0], body)
        elif len(self.assume) > 1:
            body = smt.Implies(smt.And(self.assume), body)
        if len(self.vars) == 0:
            return body
        else:
            return smt.ForAll(self.vars, body)

    def _lemma(self, rhs, by, **kwargs):
        op = self.mode.op
        l = kd.lemma(self._forall(op(self.iterm, rhs)), by=by, **kwargs)
        self.lemma = kd.kernel.lemma(
            self._forall(op(self.lhs, rhs)), by=[l, self.lemma], **kwargs
        )
        self.iterm = rhs

    def eq(self, rhs, by=[], **kwargs):
        self._lemma(rhs, by, **kwargs)
        return self

    def _set_mode(self, newmode):
        if not self.mode.trans(newmode):
            raise kd.kernel.LemmaError(
                "Cannot change from", self.mode, "to", newmode, "in Calc"
            )
        self.mode = newmode

    def le(self, rhs, by=[]):
        self._set_mode(Calc._Mode.LE)
        self._lemma(rhs, by)
        return self

    def lt(self, rhs, by=[]):
        self._set_mode(Calc._Mode.LT)
        self._lemma(rhs, by)
        return self

    def ge(self, rhs, by=[]):
        self._set_mode(Calc._Mode.GE)
        self._lemma(rhs, by)
        return self

    def gt(self, rhs, by=[]):
        self._set_mode(Calc._Mode.GT)
        self._lemma(rhs, by)
        return self

    def __repr__(self):
        return "... " + str(self.mode) + " " + repr(self.iterm)

    def qed(self, **kwargs):
        return self.lemma


simps = {}


def lemma(
    thm: smt.BoolRef,
    by: kd.kernel.Proof | Sequence[kd.kernel.Proof] = [],
    admit=False,
    timeout=1000,
    dump=False,
    solver=None,
    defns=True,
    simps=simps,
) -> kd.kernel.Proof:
    """Prove a theorem using a list of previously proved lemmas.

    In essence `prove(Implies(by, thm))`.

    :param thm: The theorem to prove.
    Args:
        thm (smt.BoolRef): The theorem to prove.
        by (list[Proof]): A list of previously proved lemmas.
        admit     (bool): If True, admit the theorem without proof.

    Returns:
        Proof: A proof object of thm

    >>> lemma(smt.BoolVal(True))
    |- True

    >>> lemma(smt.RealVal(1) >= smt.RealVal(0))
    |- 1 >= 0

    """
    if not isinstance(by, Iterable):
        by = [by]
    if admit:
        return kd.kernel.lemma(thm, by, admit=True)
    else:
        if solver is None:
            solver = config.solver
            s = solver()  # type: ignore
        else:
            s = solver()
        s.set("timeout", timeout)
        for n, p in enumerate(by):
            if not kd.kernel.is_proof(p):
                raise kd.kernel.LemmaError("In by reasons:", p, "is not a Proof object")
            s.assert_and_track(p.thm, "by_{}".format(n))
        if len(by) == 0 and defns:
            # TODO: consider pruning definitions to those in goal.
            for v in kd.kernel.defns.values():
                s.add(v.ax.thm)
        for v in simps.values():
            s.add(v)
        s.assert_and_track(smt.Not(thm), "knuckledragger_goal")
        if dump:
            print(s.sexpr())
            print(smt.solver)
            if smt.solver == smt.Z3SOLVER:
                """
                def log_instance(pr, clause, myst):
                    print(type(pr))
                    if pr.decl().name() == "inst":
                        q = pr.arg(0)
                        for ch in pr.children():
                            if ch.decl().name() == "bind":
                                print("Binding")
                                print(q)
                                print(ch.children())
                                break

                onc = smt.OnClause(s, log_instance)
                """
                smt.OnClause(s, lambda pr, clause, myst: print(pr, clause, myst))
        res = s.check()
        if res != smt.unsat:
            if res == smt.sat:
                raise kd.kernel.LemmaError(thm, by, "Countermodel", s.model())
            raise kd.kernel.LemmaError("lemma", thm, by, res)
        else:
            core = s.unsat_core()
            if smt.Bool("knuckledragger_goal") not in core:
                raise kd.kernel.LemmaError(
                    thm,
                    core,
                    "Inconsistent lemmas. Goal is not used for proof. Something has gone awry.",
                )
            if dump and len(core) < len(by) + 1:
                print("WARNING: Unneeded assumptions. Used", core, thm)
            return kd.kernel.lemma(
                thm, by, admit=admit, timeout=timeout, dump=dump, solver=solver
            )


def simp(t: smt.ExprRef, by: list[kd.kernel.Proof] = [], **kwargs) -> kd.kernel.Proof:
    rules = [kd.utils.rule_of_theorem(lem.thm) for lem in by]
    t1 = kd.utils.rewrite(t, rules)
    return lemma(smt.Eq(t, t1), by=by, **kwargs)


class Goal(NamedTuple):
    # TODO: also put eigenvariables, unification variables in here
    sig: list[smt.ExprRef]
    ctx: list[smt.BoolRef]
    goal: smt.BoolRef | smt.QuantifierRef

    def __repr__(self):
        if self.is_empty():
            return "Nothing to do!"
        if len(self.sig) == 0:
            return repr(self.ctx) + " ?|- " + repr(self.goal)
        else:
            return (
                repr([f"{v} : {v.sort()}" for v in self.sig])
                + " ; "
                + repr(self.ctx)
                + " ?|- "
                + repr(self.goal)
            )

    @classmethod
    def empty(cls) -> "Goal":
        return Goal([], [], smt.Bool("KNUCKLEDRAGGER_EMPTYGOAL"))

    def is_empty(self) -> bool:
        return self == Goal.empty()


class Lemma:
    """Tactic class for interactive proofs"""

    def __init__(self, goal: smt.BoolRef):
        self.lemmas = []
        self.thm = goal
        self.goals = [Goal(sig=[], ctx=[], goal=goal)]

    def fixes(self) -> list[smt.ExprRef]:
        """fixes opens a forall quantifier. ?|- forall x, p(x) becomes x ?|- p(x)"""
        goalctx = self.goals[-1]
        goal = goalctx.goal
        if isinstance(goal, smt.QuantifierRef) and goal.is_forall():
            self.goals.pop()
            vs, herb_lemma = kd.kernel.herb(goal)
            self.lemmas.append(herb_lemma)
            self.goals.append(
                goalctx._replace(sig=goalctx.sig + vs, goal=herb_lemma.thm.arg(0))
            )
            return vs
        else:
            raise ValueError(f"fixes tactic failed. Not a forall {goal}")

    def fix(self) -> smt.ExprRef:
        return self.fixes()[0]

    def intros(self) -> smt.ExprRef | list[smt.ExprRef] | Goal:
        """
        intros opens an implication. ?|- p -> q becomes p ?|- q

        >>> p,q,r = smt.Bools("p q r")
        >>> l = Lemma(smt.Implies(p, q))
        >>> l.intros()
        [p] ?|- q
        >>> l = Lemma(smt.Not(q))
        >>> l.intros()
        [q] ?|- False
        """
        goalctx = self.top_goal()
        goal = goalctx.goal
        ctx = goalctx.ctx
        if isinstance(goal, smt.QuantifierRef) and goal.is_forall():
            return self.fixes()
        self.goals.pop()
        if smt.is_implies(goal):
            self.goals.append(
                goalctx._replace(ctx=ctx + [goal.arg(0)], goal=goal.arg(1))
            )
            return self.top_goal()
        elif smt.is_not(goal):
            self.goals.append(
                goalctx._replace(ctx=ctx + [goal.arg(0)], goal=smt.BoolVal(False))
            )
            return self.top_goal()
        elif (
            smt.is_or(goal) and smt.is_not(goal.arg(0))
        ):  # if implies a -> b gets classically unwound to Or(Not(a), b). TODO: Maybe I should remove this
            if goal.num_args() == 2:
                self.goals.append(
                    goalctx._replace(ctx=ctx + [goal.arg(0).arg(0)], goal=goal.arg(1))
                )
            else:
                self.goals.append(
                    goalctx._replace(
                        ctx=ctx + [goal.arg(0).arg(0)], goal=smt.Or(goal.children()[1:])
                    )
                )
            return self.top_goal()
        else:
            raise ValueError("Intros failed.")

    def simp(self, at=None):
        """
        Use built in z3 simplifier. May be useful for boolean, arithmetic, lambda, and array simplifications.

        >>> x,y = smt.Ints("x y")
        >>> l = Lemma(x + y == y + x)
        >>> l.simp()
        [] ?|- True
        >>> l = Lemma(x == 3 + y + 7)
        >>> l.simp()
        [] ?|- x == 10 + y
        >>> l = Lemma(smt.Lambda([x], x + 1)[3] == y)
        >>> l.simp()
        [] ?|- 4 == y
        """
        goalctx = self.top_goal()
        if at is None:
            oldgoal = goalctx.goal
            newgoal = smt.simplify(oldgoal)
            if newgoal.eq(oldgoal):
                raise ValueError("Simplify failed. Goal is already simplified.")
            self.lemmas.append(kd.kernel.lemma(oldgoal == newgoal))
            self.goals[-1] = goalctx._replace(goal=newgoal)
        else:
            oldctx = goalctx.ctx
            old = oldctx[at]
            new = smt.simplify(old)
            if new.eq(old):
                raise ValueError("Simplify failed. Ctx is already simplified.")
            self.lemmas.append(kd.kernel.lemma(old == new))
            self.goals[-1] = goalctx._replace(
                ctx=oldctx[:at] + [new] + oldctx[at + 1 :]
            )
        return self.top_goal()

    def cases(self, t):
        """
        `cases` let's us consider an object by cases.
        We consider whether Bools are True or False
        We consider the different constructors for datatypes

        >>> import kdrag.theories.datatypes.nat as nat
        >>> x = smt.Const("x", nat.Nat)
        >>> l = Lemma(smt.BoolVal(True))
        >>> l.cases(x)
        [is(Z, x) == True] ?|- True
        """
        goalctx = self.top_goal()
        ctx = goalctx.ctx
        goal = goalctx.goal
        if t.sort() == smt.BoolSort():
            self.goals.pop()
            self.goals.append(
                goalctx._replace(ctx=ctx + [t == smt.BoolVal(True)], goal=goal)
            )
            self.goals.append(
                goalctx._replace(ctx=ctx + [t == smt.BoolVal(False)], goal=goal)
            )
        elif isinstance(t, smt.DatatypeRef):
            self.goals.pop()
            dsort = t.sort()
            for i in reversed(range(dsort.num_constructors())):
                self.goals.append(
                    goalctx._replace(
                        ctx=ctx + [dsort.recognizer(i)(t) == smt.BoolVal(True)],
                        goal=goal,
                    )
                )
        else:
            raise ValueError("Cases failed. Not a bool or datatype")
        return self.top_goal()

    def auto(self, **kwargs):
        """
        `auto` discharges a goal using z3. It forwards all parameters to `kd.lemma`
        """
        goalctx = self.goals[-1]
        ctx, goal = goalctx.ctx, goalctx.goal
        self.lemmas.append(lemma(smt.Implies(smt.And(ctx), goal), **kwargs))
        self.goals.pop()
        return self.top_goal()

    def einstan(self, n):
        """
        einstan opens an exists quantifier in context and returns the fresh eigenvariable.
        `[exists x, p(x)] ?|- goal` becomes `p(x) ?|- goal`
        """
        goalctx = self.goals[-1]
        ctx, goal = goalctx.ctx, goalctx.goal
        formula = ctx[n]
        if isinstance(formula, smt.QuantifierRef) and formula.is_exists():
            self.goals.pop()
            fs, einstan_lemma = kd.kernel.einstan(formula)
            self.lemmas.append(einstan_lemma)
            self.goals.append(
                goalctx._replace(
                    sig=goalctx.sig + fs,
                    ctx=ctx[:n] + [einstan_lemma.thm.arg(1)] + ctx[n + 1 :],
                    goal=goal,
                )
            )
            if len(fs) == 1:
                return fs[0]
            else:
                return fs
        else:
            raise ValueError("Einstan failed. Not an exists")

    def instan(self, n, *ts):
        """
        Instantiate a universal quantifier in the context.

        >>> x,y = smt.Ints("x y")
        >>> l = Lemma(smt.Implies(smt.ForAll([x],x == y), True))
        >>> l.intros()
        [ForAll(x, x == y)] ?|- True
        >>> l.instan(0, smt.IntVal(42))
        [ForAll(x, x == y), 42 == y] ?|- True
        """
        goalctx = self.goals[-1]
        thm = goalctx.ctx[n]
        if isinstance(thm, smt.QuantifierRef) and thm.is_forall():
            l = kd.kernel.instan2(ts, thm)
            self.lemmas.append(l)
            self.goals[-1] = goalctx._replace(ctx=goalctx.ctx + [l.thm.arg(1)])
            return self.top_goal()
        else:
            raise ValueError("Instan failed. Not a forall", thm)

    def ext(self):
        """
        Apply extensionality to a goal

        >>> x = smt.Int("x")
        >>> l = Lemma(smt.Lambda([x], smt.IntVal(1)) == smt.K(smt.IntSort(), smt.IntVal(1)))
        >>> _ = l.ext()
        """
        goalctx = self.top_goal()
        goal = goalctx.goal
        if smt.is_eq(goal):
            lhs, rhs = goal.arg(0), goal.arg(1)
            if smt.is_array_sort(lhs):
                self.goals.pop()
                ext_ind = smt.Ext(lhs, rhs)
                x = smt.FreshConst(ext_ind.sort())
                newgoal = smt.Eq(lhs[x], rhs[x])
                self.lemmas.append(
                    kd.kernel.lemma(
                        smt.Implies(x == ext_ind, smt.Eq(lhs, rhs) == newgoal)
                    )
                )
                self.goals.append(
                    goalctx._replace(ctx=goalctx.ctx + [x == ext_ind], goal=newgoal)
                )
                return x
            else:
                raise ValueError("Ext failed. Goal is not an array equality", goal)
        else:
            raise ValueError("Ext failed. Goal is not an equality", goal)

    def split(self, at=None):
        """
        `split` breaks apart an `And` or bi-implication `==` goal.
        The optional keyword at allows you to break apart an And or Or in the context
        """
        goalctx = self.goals[-1]
        ctx, goal = goalctx.ctx, goalctx.goal
        if at is None:
            if smt.is_and(goal):
                self.goals.pop()
                self.goals.extend(
                    [
                        goalctx._replace(ctx=ctx, goal=c)
                        for c in reversed(goal.children())
                    ]
                )
            elif smt.is_eq(goal):
                self.goals.pop()
                self.goals.append(
                    goalctx._replace(
                        ctx=ctx, goal=smt.Implies(goal.arg(0), goal.arg(1))
                    )
                )
                self.goals.append(
                    goalctx._replace(
                        ctx=ctx, goal=smt.Implies(goal.arg(1), goal.arg(0))
                    )
                )
            elif smt.is_distinct(goal):
                self.goals.pop()
                for i in range(goal.num_args()):
                    for j in range(i):
                        self.goals.append(
                            goalctx._replace(
                                ctx=ctx + [smt.Eq(goal.arg(j), goal.arg(i))],
                                goal=smt.BoolVal(False),
                            )
                        )
            else:
                raise ValueError("Unexpected case in goal for split tactic", goal)
            return self.top_goal()
        else:
            if smt.is_or(ctx[at]):
                self.goals.pop()
                for c in ctx[at].children():
                    self.goals.append(
                        goalctx._replace(ctx=ctx[:at] + [c] + ctx[at + 1 :], goal=goal)
                    )
            if smt.is_and(ctx[at]):
                self.goals.pop()
                self.goals.append(
                    goalctx._replace(
                        ctx=ctx[:at] + ctx[at].children() + ctx[at + 1 :], goal=goal
                    )
                )
            else:
                raise ValueError("Split failed")
            return self.top_goal()

    def left(self, n=0):
        """
        Select the left case of an `Or` goal.
        `?|- Or(p,q)` becomes `?|- p`
        """
        # TODO: consider adding Not(right) to context since we're classical?
        goalctx = self.goals[-1]
        ctx, goal = goalctx.ctx, goalctx.goal
        if smt.is_or(goal):
            if n is None:
                n = 0
            self.goals[-1] = goalctx._replace(ctx=ctx, goal=goal.arg(n))
            return self.top_goal()
        else:
            raise ValueError("Left failed. Not an or")

    def right(self):
        """
        Select the right case of an `Or` goal.
        `?|- Or(p,q)` becomes `?|- q`
        """
        goalctx = self.goals[-1]
        ctx, goal = goalctx.ctx, goalctx.goal
        if smt.is_or(goal):
            self.goals[-1] = goalctx._replace(
                ctx=ctx, goal=goal.arg(goal.num_args() - 1)
            )
            return self.top_goal()
        else:
            raise ValueError("Right failed. Not an or")

    def exists(self, *ts):
        """
        Give terms `ts` to satisfy an exists goal
        `?|- exists x, p(x)` becomes `?|- p(ts)`

        >>> x,y = smt.Ints("x y")
        >>> Lemma(smt.Exists([x], x == y)).exists(y)
        [] ?|- y == y
        """
        goalctx = self.goals[-1]
        ctx, goal = goalctx.ctx, goalctx.goal
        assert isinstance(goal, smt.QuantifierRef) and goal.is_exists()
        lemma = kd.kernel.forget2(ts, goal)
        self.lemmas.append(lemma)
        self.goals[-1] = goalctx._replace(ctx=ctx, goal=lemma.thm.arg(0))
        return self.top_goal()

    def rewrite(self, rule: kd.kernel.Proof | int, at=None, rev=False):
        """
        `rewrite` allows you to apply rewrite rule (which may either be a Proof or an index into the context) to the goal or to the context.
        """
        goalctx = self.goals[-1]
        ctx, goal = goalctx.ctx, goalctx.goal
        if isinstance(rule, int):
            rulethm = ctx[rule]
        elif kd.kernel.is_proof(rule):
            rulethm = rule.thm
        else:
            raise ValueError(
                "Rewrite tactic failed. Not a proof or context index", rule
            )
        if isinstance(rulethm, smt.QuantifierRef) and rulethm.is_forall():
            vs, body = kd.utils.open_binder(rulethm)
        else:
            vs = []
            body = rulethm
        if smt.is_eq(body):
            lhs, rhs = body.arg(0), body.arg(1)
            if rev:
                lhs, rhs = rhs, lhs
        else:
            raise ValueError(f"Rewrite tactic failed. Not an equality {rulethm}")
        if at is None:
            target = goal
        elif isinstance(at, int):
            target = ctx[at]
        else:
            raise ValueError(
                "Rewrite tactic failed. `at` is not an index into the context"
            )
        subst = kd.utils.pmatch_rec(vs, lhs, target)
        if subst is None:
            raise ValueError(
                f"Rewrite tactic failed to apply lemma {rulethm} to goal {goal}"
            )
        else:
            self.goals.pop()
            lhs1 = smt.substitute(lhs, *[(v, t) for v, t in subst.items()])
            rhs1 = smt.substitute(rhs, *[(v, t) for v, t in subst.items()])
            target: smt.BoolRef = smt.substitute(target, (lhs1, rhs1))
            if isinstance(rulethm, smt.QuantifierRef) and rulethm.is_forall():
                self.lemmas.append(kd.kernel.instan2([subst[v] for v in vs], rulethm))
            if not isinstance(rule, int) and kd.kernel.is_proof(rule):
                self.lemmas.append(rule)
            if at is None:
                self.goals.append(goalctx._replace(ctx=ctx, goal=target))
            else:
                if at == -1:
                    at = len(ctx) - 1
                self.goals.append(
                    goalctx._replace(ctx=ctx[:at] + [target] + ctx[at + 1 :], goal=goal)
                )
            return self.top_goal()

    def rw(self, rule: kd.kernel.Proof | int, at=None, rev=False):
        """
        shorthand for rewrite
        """
        return self.rewrite(rule, at=at, rev=rev)

    def symm(self):
        """
        Swap left and right hand side of equational goal

        >>> x,y = smt.Ints("x y")
        >>> Lemma(x == y).symm()
        [] ?|- y == x
        """
        ctxgoal = self.top_goal()
        if smt.is_eq(ctxgoal.goal):
            self.goals[-1] = ctxgoal._replace(
                goal=smt.Eq(ctxgoal.goal.arg(1), ctxgoal.goal.arg(0))
            )
            return self.top_goal()
        else:
            raise ValueError("Symm tactic failed. Not an equality", ctxgoal.goal)

    def eq(self, rhs: smt.ExprRef, **kwargs):
        """replace rhs in equational goal"""
        # TODO: consider allow `by` keyword to reference context`
        ctxgoal = self.top_goal()
        if smt.is_eq(ctxgoal.goal):
            self.lemmas.append(
                kd.kernel.lemma(
                    smt.Implies(smt.And(ctxgoal.ctx), ctxgoal.goal.arg(1) == rhs),
                    **kwargs,
                )
            )
            self.goals[-1] = ctxgoal._replace(goal=smt.Eq(ctxgoal.goal.arg(0), rhs))
            return self.top_goal()
        else:
            raise ValueError("Eq tactic failed. Not an equality", ctxgoal.goal)

    def newgoal(self, newgoal: smt.BoolRef, **kwargs):
        """
        Try to show newgoal is sufficient to prove current goal
        """
        goalctx = self.top_goal()
        self.lemmas.append(
            kd.lemma(
                smt.Implies(smt.And(goalctx.ctx + [newgoal]), goalctx.goal), **kwargs
            )
        )
        self.goals[-1] = goalctx._replace(goal=newgoal)
        return self.top_goal()

    def unfold(self, *decls: smt.FuncDeclRef, at=None):
        """
        Unfold the contents of a definition.
        """
        goalctx = self.top_goal()
        decls1 = None if len(decls) == 0 else decls
        if at is None:
            e = goalctx.goal
            e2 = kd.utils.unfold(e, decls=decls1, trace=self.lemmas)
            self.goals.pop()
            self.goals.append(goalctx._replace(goal=e2))
        else:
            e = goalctx.ctx[at]
            e2 = kd.utils.unfold(e, decls=decls, trace=self.lemmas)
            self.goals.pop()
            if at == -1:
                at = len(goalctx.ctx) - 1
            self.goals.append(
                goalctx._replace(ctx=goalctx.ctx[:at] + [e2] + goalctx.ctx[at + 1 :])
            )

        return self.top_goal()

    def apply(self, pf: kd.kernel.Proof, rev=False):
        """
        `apply` matches the conclusion of a proven clause
        """
        goalctx = self.goals.pop()
        ctx, goal = goalctx.ctx, goalctx.goal
        thm = pf.thm
        if isinstance(thm, smt.QuantifierRef) and thm.is_forall():
            vs, thm = kd.utils.open_binder(thm)
        else:
            vs = []
        if smt.is_implies(thm):
            pat = thm.arg(1)
        elif smt.is_eq(thm):
            if rev:
                pat = thm.arg(1)
            else:
                pat = thm.arg(0)
        else:
            pat = thm
        subst = kd.utils.pmatch(vs, pat, goal)
        if subst is None:
            raise ValueError(f"Apply tactic failed to apply lemma {pf} to goal {goal} ")
        else:
            if len(vs) > 0:
                pf1 = kd.kernel.instan([subst[v] for v in vs], pf)
                self.lemmas.append(pf1)
            else:
                pf1 = pf
            if smt.is_implies(pf1.thm):
                self.goals.append(goalctx._replace(ctx=ctx, goal=pf1.thm.arg(0)))
            elif smt.is_eq(pf1.thm):
                if rev:
                    self.goals.append(goalctx._replace(ctx=ctx, goal=pf1.thm.arg(0)))
                else:
                    self.goals.append(goalctx._replace(ctx=ctx, goal=pf1.thm.arg(1)))
        return self.top_goal()

    def induct(
        self,
        x: smt.ExprRef,
        using: Optional[
            Callable[
                [smt.ExprRef, Callable[[smt.ExprRef, smt.BoolRef], smt.BoolRef]],
                kd.kernel.Proof,
            ]
        ] = None,
    ):
        """
        Apply an induction lemma instantiated on x.
        """
        goal = self.top_goal().goal
        if using is None:
            indlem = x.induct(smt.Lambda([x], goal))
        else:
            indlem = using(x, smt.Lambda([x], goal))
        self.lemmas.append(indlem)
        self.apply(indlem)
        if smt.is_and(self.top_goal().goal):
            # self.split()
            goalctx = self.goals.pop()
            self.goals.extend(
                [goalctx._replace(goal=c) for c in reversed(goalctx.goal.children())]
            )
        return self.top_goal()

    def clear(self, n: int):
        """
        Remove a hypothesis from the context
        """
        ctxgoal = self.goals[-1]
        ctxgoal.ctx.pop(n)
        return self.top_goal()

    def generalize(self, *vs: smt.ExprRef):
        """
        Put variables forall quantified back on goal. Useful for strengthening induction hypotheses.
        """
        goalctx = self.goals.pop()
        self.lemmas.append(kd.kernel.instan2(vs, smt.ForAll(vs, goalctx.goal)))
        self.goals.append(goalctx._replace(goal=smt.ForAll(vs, goalctx.goal)))
        return self.top_goal()

    def show(self, thm: smt.BoolRef):
        """
        To document the current goal
        """
        goal = self.top_goal().goal
        if not thm.eq(goal):
            raise ValueError("Goal does not match", thm, goal)
        return self.top_goal()

    def assumption(self):
        """
        Exact match of goal in the context
        """
        goalctx = self.goals.pop()
        goal, ctx = goalctx.goal, goalctx.ctx
        if any([goal.eq(h) for h in ctx]):
            return self.top_goal()
        else:
            raise ValueError("Assumption tactic failed", goal, ctx)

    def have(self, conc: smt.BoolRef, **kwargs):
        """
        Prove the given formula and add it to the current context
        """
        goalctx = self.goals.pop()
        self.lemmas.append(
            kd.kernel.lemma(smt.Implies(smt.And(goalctx.ctx), conc), **kwargs)
        )
        self.goals.append(goalctx._replace(ctx=goalctx.ctx + [conc]))
        return self.top_goal()

    def admit(self) -> Goal:
        """
        admit the current goal without proof. Don't feel bad about keeping yourself moving, but be aware that you're not done.

        >>> l = Lemma(smt.BoolVal(False)) # a false goal
        >>> _ = l.admit()
        >>> l.qed()
        |- False
        """
        goalctx = self.goals.pop()
        self.lemmas.append(kd.kernel.lemma(goalctx.goal, admit=True))
        return self.top_goal()

    # TODO
    # def search():
    # def calc

    def top_goal(self) -> Goal:
        if len(self.goals) == 0:
            return Goal.empty()  # kind of hacky
        return self.goals[-1]

    def __repr__(self):
        if len(self.goals) == 0:
            return "Nothing to do. Hooray!"
        return repr(self.top_goal())

    def qed(self, **kwargs) -> kd.kernel.Proof:
        """
        return the actual final `Proof` of the lemma that was defined at the beginning.
        """

        if "by" in kwargs:
            kwargs["by"].extend(self.lemmas)
        else:
            kwargs["by"] = self.lemmas
        return kd.kernel.lemma(self.thm, **kwargs)
