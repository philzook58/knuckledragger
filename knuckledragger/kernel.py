import z3
from dataclasses import dataclass
from typing import Any


@dataclass(frozen=True)
class Proof:
    thm: z3.BoolRef
    reason: list[Any]
    admit: bool


__Proof = Proof
Proof = None


def lemma(thm, by=[], admit=False):
    if admit:
        print("Admitting lemma {}".format(thm))
        return __Proof(thm, by, True)
    else:
        s = z3.Solver()
        for p in by:
            assert isinstance(p, __Proof)
            s.add(p.thm)
        s.add(z3.Not(thm))
        res = s.check()
        if res != z3.unsat:
            print(s.sexpr())
            if res == z3.sat:
                print(s.model())
            assert False, res
        return __Proof(thm, by, False)


def axiom(thm, reason):
    return __Proof(thm, reason, admit=True)
