import z3
from dataclasses import dataclass
from typing import Any


@dataclass(frozen=True)
class Proof:
    thm: z3.BoolRef
    reason: list[Any]
    admit: bool


# It is unlikely that users should be accessing `Proof` directly.
# This is not ironclad. If you really want the Proof constructor, I can't stop you.
__Proof = Proof
Proof = None


def lemma(thm: z3.BoolRef, by: list[Proof] = [], admit=False) -> Proof:
    """Prove a theorem using a list of previously proved lemmas.

    In essence `prove(Implies(by, thm))`.

    Args:
        thm: The theorem to prove.
        by: A list of previously proved lemmas.
        admit: If True, admit the theorem without proof.

    >>> lemma(BoolVal(True))

    >>> lemma(RealVal(1) >= RealVal(0))

    """
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


def axiom(thm: z3.BoolRef, reason=None) -> Proof:
    """Assert an axiom.

    Axioms are necessary and useful. But you must use great care.

    Args:
        thm: The axiom to assert.
        reason: A python object explaining why the axiom should exist. Often a string explaining the axiom.
    """
    return __Proof(thm, reason, admit=True)
