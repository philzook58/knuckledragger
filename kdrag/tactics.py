from re import L
import kdrag as kd
import kdrag.smt as smt
from enum import IntEnum
import operator as op
from . import config


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


class Lemma:
    # Isar style forward proof
    def __init__(self, goal: smt.BoolRef):
        # self.cur_goal = goal
        self.lemmas = []
        self.thm = goal
        self.goals = [([], goal)]

    def intros(self):
        ctx, goal = self.goals.pop()
        if smt.is_quantifier(goal) and goal.is_forall():
            vs, herb_lemma = kd.kernel.herb(goal)
            self.lemmas.append(herb_lemma)
            self.goals.append((ctx, herb_lemma.thm.arg(0)))
            return vs
        elif smt.is_implies(goal):
            self.goals.append((ctx + [goal.arg(0)], goal.arg(1)))
            return self

    def cases(self, t):
        ctx, goal = self.goals.pop()
        if t.sort() == smt.BoolSort():
            self.goals.append((ctx + [smt.Not(t)], goal))
            self.goals.append((ctx + [t], goal))
        elif isinstance(t, smt.DatatypeRef):
            dsort = t.sort()
            for i in reversed(range(dsort.num_constructors())):
                self.goals.append((ctx + [dsort.recognizer(i)(t)], goal))
        else:
            raise ValueError("Cases failed. Not a bool or datatype")
        return self

    def auto(self):
        ctx, goal = self.goals[-1]
        self.lemmas.append(lemma(smt.Implies(smt.And(ctx), goal)))
        self.goals.pop()
        return self

    def split(self):
        ctx, goal = self.goals[-1]
        if smt.is_and(goal):
            self.goals.pop()
            self.goals.extend([(ctx, c) for c in goal.children()])
        else:
            raise ValueError("Split failed. Not an and")

    def exists(self, *ts):
        ctx, goal = self.goals[-1]
        lemma = kd.kernel.forget2(ts, goal)
        self.lemmas.append(lemma)
        self.goals[-1] = (ctx, lemma.thm.arg(0))
        return self

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
                self.goals.append((ctx, pf1.thm.arg(0)))
            elif smt.is_eq(pf1.thm):
                if rev:
                    self.goals.append((ctx, pf1.thm.arg(0)))
                else:
                    self.goals.append((ctx, pf1.thm.arg(1)))
        return self

    def assumption(self):
        ctx, goal = self.goals.pop()
        if any([goal.eq(h) for h in ctx]):
            return self
        else:
            raise ValueError("Assumption tactic failed", goal, ctx)

    def have(self, conc, **kwargs):
        ctx, goal = self.goals.pop()
        self.lemmas.append(lemma(smt.Implies(smt.And(ctx), conc)), **kwargs)
        self.goals.append((ctx + [conc], conc))
        return self

    def __repr__(self):
        if len(self.goals) == 0:
            return "Nothing to do. Hooray!"
        ctx, goal = self.goals[-1]
        return repr(ctx) + " ?|- " + repr(goal)

    def qed(self):
        return lemma(self.thm, by=self.lemmas)
