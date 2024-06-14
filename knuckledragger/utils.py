from knuckledragger.kernel import lemma, is_proof
import z3
from operator import eq


def calc(*args, vars=None, by=[], op=eq):
    """
    calc is for equational reasoning.
    One can write a sequence of formulas interspersed with useful lemmas.
    Inequational chaining can be done via op=lambda x,y: x <= y
    """

    def thm(lhs, rhs):
        if vars == None:
            return op(lhs, rhs)
        else:
            return z3.ForAll(vars, op(lhs, rhs))

    lemmas = []
    local_by = []
    lhs = args[0]
    for arg in args[1:]:
        if is_proof(arg):
            local_by.append(arg)
        else:
            lemmas.append(lemma(thm(lhs, arg), by=by + local_by))
            lhs = arg
            local_by = []
    return lemma(thm(args[0], args[-1]), by=by + lemmas)


def lemma_smt(thm: z3.BoolRef, by=[], sig=[]) -> list[str]:
    """
    Replacement for lemma that returns smtlib string for experimentation with other solvers
    """
    output = []
    output.append(";;declarations")
    for f in sig:
        output.append(f.sexpr())
    output.append(";;axioms")
    for e in by:
        output.append("(assert " + e.sexpr() + ")")
    output.append(";;goal")
    output.append("(assert " + z3.Not(thm).sexpr() + ")")
    output.append("(check-set)")
    return output
