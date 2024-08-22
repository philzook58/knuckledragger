import knuckledragger as kd
import knuckledragger.smt as smt
from enum import IntEnum
import operator as op


class Calc:
    """
    calc is for equational reasoning.
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

    def __init__(self, vars, lhs, assume=[]):
        self.vars = vars
        self.terms = [lhs]
        self.lemmas = []
        self.assume = assume
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

    def eq(self, rhs, by=[]):
        self.lemmas.append(kd.lemma(self._forall(self.terms[-1] == rhs), by=by))
        self.terms.append(rhs)
        return self

    def _set_mode(self, newmode):
        if not self.mode.trans(newmode):
            raise kd.kernel.LemmaError(
                "Cannot change from", self.mode, "to", newmode, "in Calc"
            )
        self.mode = newmode

    def le(self, rhs, by=[]):
        self._set_mode(Calc._Mode.LE)
        self.lemmas.append(kd.lemma(self._forall(self.terms[-1] <= rhs), by=by))
        self.terms.append(rhs)
        return self

    def lt(self, rhs, by=[]):
        self._set_mode(Calc._Mode.LT)
        self.lemmas.append(kd.lemma(self._forall(self.terms[-1] < rhs), by=by))
        self.terms.append(rhs)
        return self

    def ge(self, rhs, by=[]):
        self._set_mode(Calc._Mode.GE)
        self.lemmas.append(kd.lemma(self._forall(self.terms[-1] >= rhs), by=by))
        self.terms.append(rhs)
        return self

    def gt(self, rhs, by=[]):
        self._set_mode(Calc._Mode.GT)
        self.lemmas.append(kd.lemma(self._forall(self.terms[-1] > rhs), by=by))
        self.terms.append(rhs)
        return self

    def __repr__(self):
        return "... " + str(self.mode) + " " + repr(self.terms[-1])

    def qed(self, **kwargs):
        return kd.lemma(
            self._forall(self.mode.op(self.terms[0], self.terms[-1])),
            by=self.lemmas,
            **kwargs,
        )


simps = {}


def lemma(
    thm: smt.BoolRef,
    by: list[kd.kernel.Proof] = [],
    admit=False,
    timeout=1000,
    dump=False,
    solver=smt.Solver,
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
        res = s.check()
        if res != smt.unsat:
            if res == smt.sat:
                raise kd.kernel.LemmaError(thm, by, "Countermodel", s.model())
            raise kd.kernel.LemmaError("lemma", thm, by, res)
        else:
            core = s.unsat_core()
            if not smt.Bool("knuckledragger_goal") in core:
                raise kd.kernel.LemmaError(
                    thm,
                    core,
                    "Inconsistent lemmas. Goal is not used for proof. Something has gone awry.",
                )
            if len(core) < len(by) + 1:
                print("WARNING: Unneeded assumptions. Used", core, thm)
            return kd.kernel.lemma(
                thm, by, admit=admit, timeout=timeout, dump=dump, solver=solver
            )
