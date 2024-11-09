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

    def _lemma(self, rhs, by):
        op = self.mode.op
        l = kd.lemma(self._forall(op(self.iterm, rhs)), by=by)
        self.lemma = kd.kernel.lemma(
            self._forall(op(self.lhs, rhs)), by=[l, self.lemma]
        )
        self.iterm = rhs

    def eq(self, rhs, by=[]):
        self._lemma(rhs, by)
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
    def __init__(self, goal):
        self.goal = goal
        self.lemmas = []
        self.vars = []
        self.hyps = []

    def intro(self, vars):  # fix
        self.vars.extend(vars)
        return self

    def assume(self, hyps):
        self.hyps.extend(hyps)
        return self

    def _wrap(self, form):
        return smt.ForAll(self.vars, smt.Implies(smt.And(self.hyps), form))

    def have(self, conc, **kwargs):
        self.lemmas.append(lemma(self._wrap(conc), **kwargs))
        return self

    def qed(self):
        return lemma(self.goal, by=self.lemmas)


class Lemma2:
    # Isar style forward proof
    def __init__(self, goal: smt.BoolRef):
        self.cur_goal = goal
        self.lemmas = []
        self.thm = goal

    def intros(self):
        vs, goal = kd.kernel.herb(self.cur_goal)
        self.lemmas.append(goal)
        self.cur_goal = goal.thm.arg(0)
        return vs

    def exists(self, t):
        kd.kernel.forget(self.goal, t)

    def apply(self, pf: kd.kernel.Proof):
        pass
        # TODO.
        # self.lemmas.append(pf)
        # self.cur_goal = pf.thm.arg(0)
        # return self

    def assume(self, hyps):
        self.goal.arg(0)
        return self

    def _wrap(self, form):
        return smt.ForAll(self.vars, smt.Implies(smt.And(self.hyps), form))

    def have(self, conc, **kwargs):
        self.lemmas.append(lemma(self._wrap(conc), **kwargs))
        return self

    def __repr__(self):
        return "?|- " + repr(self.cur_goal)

    def qed(self):
        return lemma(self.thm, by=self.lemmas)
