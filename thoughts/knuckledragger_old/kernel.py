from typing import Any, Tuple, List
from smt import *
import subprocess

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


__proof_db = []


def check(thm: Thm):
    """Check that a theorem hashes against secret key"""
    hsh, form = thm
    assert hsh == hash(("secret", form))


def trust(form: Form) -> Thm:
    """Trust a formula as a theorem by adding a hash"""
    return hash(("secret", form)), form


def infer(hyps: List[Thm], conc: Form, timeout=1000) -> Thm:
    """Use smt as giant inference step"""
    s = Solver()
    for hyp in hyps:
        check(hyp)
        s.add(hyp[1])
    s.add(Not(conc))
    s.set("timeout", timeout)
    res = s.check()
    if res != smt.unsat:
        print(s.sexpr())
        if res == smt.sat:
            print(s.model())
        assert False, res
    return trust(conc)


def define(name, x):
    """A definition mechanism. A Fresh constant with theorem defining it"""
    f = FreshConst(x.sort(), prefix=name)
    return f, trust(f == x)


def infer_ext(hyps: List[Thm], conc: Form, command=None, timeout=1000) -> Thm:
    s = Solver()
    for hyp in hyps:
        check(hyp)
        s.add(hyp[1])
    s.add(Not(conc))
    # TODO use better temporary file
    with open("/tmp/temp.smt2", "w") as f:
        f.write(s.sexpr())
    command.append("/tmp/temp.smt2")
    print(s.sexpr())
    res = subprocess.run(
        ["vampire", "--output_mode", "smtcomp"],
        timeout=1.0,
        capture_output=True,
    )
    print(res)
    if "unsat" not in res.stdout.decode("utf-8"):
        print(res.stdout.decode("utf-8"))
        assert False
    return trust(conc)


def infer_vampire(hyps: List[Thm], conc: Form, timeout=1000) -> Thm:
    return infer_ext(
        hyps, conc, command=["vampire", "--output_mode", "smtcomp"], timeout=timeout
    )
