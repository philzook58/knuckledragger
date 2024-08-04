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
