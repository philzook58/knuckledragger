import knuckledragger as kd
import z3


class Calc:
    """
    calc is for equational reasoning.
    One can write a sequence of formulas interspersed with useful lemmas.
    """

    def __init__(self, vars, lhs):
        # TODO: hyps=None for conditional rewriting. assumpt, assume=[]
        self.vars = vars
        self.terms = [lhs]
        self.lemmas = []

    def ForAll(self, body):
        if len(self.vars) == 0:
            return body
        else:
            return z3.ForAll(self.vars, body)

    def eq(self, rhs, by=[]):
        self.lemmas.append(kd.lemma(self.ForAll(self.terms[-1] == rhs), by=by))
        self.terms.append(rhs)
        return self

    # TODO: lt, le, gt, ge chaining. Or custom op.

    def __repr__(self):
        return "... = " + repr(self.terms[-1])

    def qed(self):
        return kd.lemma(self.ForAll(self.terms[0] == self.terms[-1]), by=self.lemmas)


def lemma(
    thm: z3.BoolRef,
    by: list[kd.kernel.Proof] = [],
    admit=False,
    timeout=1000,
    dump=False,
    solver=z3.Solver,
) -> kd.kernel.Proof:
    """Prove a theorem using a list of previously proved lemmas.

    In essence `prove(Implies(by, thm))`.

    :param thm: The theorem to prove.
    Args:
        thm (z3.BoolRef): The theorem to prove.
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
        s.assert_and_track(z3.Not(thm), "knuckledragger_goal")
        if dump:
            print(s.sexpr())
        res = s.check()
        if res != z3.unsat:
            if res == z3.sat:
                raise kd.kernel.LemmaError(thm, "Countermodel", s.model())
            raise kd.kernel.LemmaError("lemma", thm, res)
        else:
            core = s.unsat_core()
            if not z3.Bool("knuckledragger_goal") in core:
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
