from typing import Any, Tuple, List
from z3 import *

Form = Any
Thm = Tuple[int, Form]

"""
Helpful Operator Syntax
"""
BoolRef.__and__ = lambda self, other: And(self, other)
BoolRef.__or__ = lambda self, other: Or(self, other)
BoolRef.__invert__ = lambda self: Not(self)


def QForAll(vars, hyp, conc):
    """Quantified ForAll"""
    return ForAll(vars, Implies(hyp, conc))


record_proofs = False


def check(thm: Thm):
    """Check that a theorem hashes against secret key"""
    hsh, form = thm
    assert hsh == hash(("secret", form))


def trust(form: Form) -> Thm:
    """Trust a formula as a theorem by adding a hash"""
    return hash(("secret", form)), form


def infer(hyps: List[Thm], conc: Form, timeout=1000) -> Thm:
    """Use Z3 as giant inference step"""
    s = Solver()
    for hyp in hyps:
        check(hyp)
        s.add(hyp[1])
    s.add(Not(conc))
    s.set("timeout", timeout)
    res = s.check()
    if res != z3.unsat:
        print(s.sexpr())
        if res == z3.sat:
            print(s.model())
        assert False, res
    return trust(conc)


def define(name, x):
    """A definition mechanism. A Fresh constant with theorem defining it"""
    f = FreshConst(x.sort(), prefix=name)
    return f, trust(f == x)
