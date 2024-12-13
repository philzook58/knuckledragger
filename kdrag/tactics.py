from re import L
import kdrag as kd
import kdrag.smt as smt
from enum import IntEnum
import operator as op
from . import config
from typing import NamedTuple


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
        self.lemma = kd.kernel.lemma(self._forall(lhs == lhs))
        self.mode = self._Mode.EQ

    def _forall(self, body):
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
        return "... " + str(self.mode) + " " + repr(self.terms[-1])

    def qed(self, **kwargs):
        return self.lemma


simps = {}


def lemma(
    thm: smt.BoolRef,
    by: list[kd.kernel.Proof] = [],
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

    >>> lemma(BoolVal(True))

    >>> lemma(RealVal(1) >= RealVal(0))

    """
    if admit:
        return kd.kernel.lemma(
            thm, by, admit=admit, timeout=timeout, dump=dump, solver=solver
        )
    else:
        if solver is None:
            solver = config.solver
        s = solver()
        s.set("timeout", timeout)
        for n, p in enumerate(by):
            if not kd.kernel.is_proof(p):
                raise kd.kernel.LemmaError("In by reasons:", p, "is not a Proof object")
            s.assert_and_track(p.thm, "by_{}".format(n))
        if defns:
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
                onc = smt.OnClause(s, lambda pr, clause, myst: print(pr, clause, myst))
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
    return lemma(t == t1, by=by, **kwargs)


class Sequent(NamedTuple):
    ctx: list[smt.BoolRef]
    goal: smt.BoolRef

    def __repr__(self):
        return repr(self.ctx) + " ?|- " + repr(self.goal)


class Lemma:
    def __init__(self, goal: smt.BoolRef):
        self.lemmas = []
        self.thm = goal
        self.goals = [Sequent([], goal)]

    def fixes(self):
        ctx, goal = self.goals[-1]
        if smt.is_quantifier(goal) and goal.is_forall():
            self.goals.pop()
            vs, herb_lemma = kd.kernel.herb(goal)
            self.lemmas.append(herb_lemma)
            self.goals.append(Sequent(ctx, herb_lemma.thm.arg(0)))
            return vs
        else:
            raise ValueError(f"fixes tactic failed. Not a forall {goal}")

    def intros(self):
        ctx, goal = self.goals.pop()
        if smt.is_quantifier(goal) and goal.is_forall():
            vs, herb_lemma = kd.kernel.herb(goal)
            self.lemmas.append(herb_lemma)
            self.goals.append(Sequent(ctx, herb_lemma.thm.arg(0)))
            if len(vs) == 1:
                return vs[0]
            else:
                return vs
        elif smt.is_implies(goal):
            self.goals.append(Sequent(ctx + [goal.arg(0)], goal.arg(1)))
            return self.top_goal()
        elif smt.is_not(goal):
            self.goals.append((ctx + [goal.arg(0)], smt.BoolVal(False)))
            return
        else:
            raise ValueError("Intros failed.")

    def cases(self, t):
        ctx, goal = self.goals.pop()
        if t.sort() == smt.BoolSort():
            self.goals.append(Sequent(ctx + [smt.Not(t)], goal))
            self.goals.append(Sequent(ctx + [t], goal))
        elif isinstance(t, smt.DatatypeRef):
            dsort = t.sort()
            for i in reversed(range(dsort.num_constructors())):
                self.goals.append(Sequent(ctx + [dsort.recognizer(i)(t)], goal))
        else:
            raise ValueError("Cases failed. Not a bool or datatype")
        return self.top_goal()

    def auto(self):
        ctx, goal = self.goals[-1]
        self.lemmas.append(lemma(smt.Implies(smt.And(ctx), goal)))
        self.goals.pop()
        return self.top_goal()

    def einstan(self, n):
        ctx, goal = self.goals[-1]
        formula = ctx[n]
        if smt.is_quantifier(formula) and formula.is_exists():
            self.goals.pop()
            fs, einstan_lemma = kd.kernel.einstan(formula)
            self.lemmas.append(einstan_lemma)
            self.goals.append(
                Sequent(ctx[:n] + [einstan_lemma.thm.arg(1)] + ctx[n + 1 :], goal)
            )
            if len(fs) == 1:
                return fs[0]
            else:
                return fs
        else:
            raise ValueError("Einstan failed. Not an exists")

    def split(self, at=None):
        ctx, goal = self.goals[-1]
        if at is None:
            if smt.is_and(goal):
                self.goals.pop()
                self.goals.extend([Sequent(ctx, c) for c in goal.children()])
            if smt.is_eq(goal):
                self.goals.pop()
                self.goals.append(Sequent(ctx, smt.Implies(goal.arg(0), goal.arg(1))))
                self.goals.append(Sequent(ctx, smt.Implies(goal.arg(1), goal.arg(0))))
            else:
                raise ValueError("Split failed")
        else:
            if smt.is_or(ctx[at]):
                self.goals.pop()
                for c in ctx[at].children():
                    self.goals.append(Sequent(ctx[:at] + [c] + ctx[at + 1 :], goal))
            if smt.is_and(ctx[at]):
                self.goals.pop()
                self.goals.append(
                    Sequent(ctx[:at] + ctx[at].children() + ctx[at + 1 :], goal)
                )
            else:
                raise ValueError("Split failed")

    def left(self, n=0):
        ctx, goal = self.goals[-1]
        if smt.is_or(goal):
            if n is None:
                n = 0
            self.goals[-1] = Sequent(ctx, goal.arg(n))
            return self.top_goal()
        else:
            raise ValueError("Left failed. Not an or")

    def right(self):
        ctx, goal = self.goals[-1]
        if smt.is_or(goal):
            self.goals[-1] = Sequent(ctx, goal.arg(goal.num_args() - 1))
            return self.top_goal()
        else:
            raise ValueError("Right failed. Not an or")

    def exists(self, *ts):
        ctx, goal = self.goals[-1]
        lemma = kd.kernel.forget2(ts, goal)
        self.lemmas.append(lemma)
        self.goals[-1] = Sequent(ctx, lemma.thm.arg(0))
        return self.top_goal()

    def rewrite(self, rule, at=None, rev=False):
        """
        `rewrite` allows you to apply rewrite rule (which may either be a Proof or an index into the context) to the goal or to the context.
        """
        ctx, goal = self.goals[-1]
        if isinstance(rule, int):
            rulethm = ctx[rule]
        elif kd.kernel.is_proof(rule):
            rulethm = rule.thm
        if smt.is_quantifier(rulethm) and rulethm.is_forall():
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
            self.lemmas.append(kd.kernel.instan2([subst[v] for v in vs], rulethm))
            if kd.kernel.is_proof(rule):
                self.lemmas.append(rule)
            if at is None:
                self.goals.append(Sequent(ctx, target))
            else:
                self.goals.append(Sequent(ctx[:at] + [target] + ctx[at + 1 :], goal))
            return self.top_goal()

    def rw(self, rule, at=None, rev=False):
        return self.rewrite(rule, at=at, rev=rev)

    def unfold(self, decl: smt.FuncDeclRef):
        if hasattr(decl, "defn"):
            return self.rewrite(decl.defn)
        else:
            raise ValueError("Unfold failed. Not a defined function")

    def apply(self, pf: kd.kernel.Proof, rev=False):
        ctx, goal = self.goals.pop()
        thm = pf.thm
        if smt.is_quantifier(thm) and thm.is_forall():
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
            pf1 = kd.kernel.instan([subst[v] for v in vs], pf)
            self.lemmas.append(pf1)
            if smt.is_implies(pf1.thm):
                self.goals.append(Sequent(ctx, pf1.thm.arg(0)))
            elif smt.is_eq(pf1.thm):
                if rev:
                    self.goals.append(Sequent(ctx, pf1.thm.arg(0)))
                else:
                    self.goals.append(Sequent(ctx, pf1.thm.arg(1)))
        return self.top_goal()

    def assumption(self):
        ctx, goal = self.goals.pop()
        if any([goal.eq(h) for h in ctx]):
            return self.top_goal()
        else:
            raise ValueError("Assumption tactic failed", goal, ctx)

    def have(self, conc, **kwargs):
        ctx, goal = self.goals.pop()
        self.lemmas.append(lemma(smt.Implies(smt.And(ctx), conc)), **kwargs)
        self.goals.append(Sequent(ctx + [conc], conc))
        return self.top_goal()

    # TODO
    # def search():
    # def calc

    def top_goal(self):
        if len(self.goals) == 0:
            return "Nothing to do. Hooray!"
        return self.goals[-1]

    def __repr__(self):
        return repr(self.top_goal())

    def qed(self):
        return kd.kernel.lemma(self.thm, by=self.lemmas)
