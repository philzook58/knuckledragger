import z3
from dataclasses import dataclass
from typing import Any


@dataclass(frozen=True)
class Proof(z3.Z3PPObject):
    thm: z3.BoolRef
    reason: list[Any]
    admit: bool

    def __repr__(self):
        return "&ctdot; &#8870;" + repr(self.thm)


# It is unlikely that users should be accessing the `Proof` constructor directly.
# This is not ironclad. If you really want the Proof constructor, I can't stop you.
__Proof = Proof
Proof = None


class LemmaError(Exception):
    pass


def lemma(thm: z3.BoolRef, by: list[Proof] = [], admit=False) -> Proof:
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
        print("Admitting lemma {}".format(thm))
        return __Proof(thm, by, True)
    else:
        s = z3.Solver()
        for p in by:
            if not isinstance(p, __Proof):
                raise LemmaError("In by reasons:", p, "is not a Proof object")
            s.add(p.thm)
        s.add(z3.Not(thm))
        res = s.check()
        if res != z3.unsat:
            if res == z3.sat:
                raise LemmaError(thm, "Countermodel", s.model())
            raise LemmaError("lemma", thm, res)
        return __Proof(thm, by, False)


def axiom(thm: z3.BoolRef, reason=[]) -> Proof:
    """Assert an axiom.

    Axioms are necessary and useful. But you must use great care.

    Args:
        thm: The axiom to assert.
        reason: A python object explaining why the axiom should exist. Often a string explaining the axiom.
    """
    return __Proof(thm, reason, admit=False)


__sig = {}


def define(
    name: str, args: list[z3.ExprRef], defn: z3.ExprRef
) -> tuple[z3.FuncDeclRef, __Proof]:
    """Define a non recursive definition. Useful for shorthand and abstraction.

    Args:
        name: The name of the term to define.
        args: The arguments of the term.
        defn: The definition of the term.

    Returns:
        tuple[z3.FuncDeclRef, __Proof]: A tuple of the defined term and the proof of the definition.
    """
    sorts = [arg.sort() for arg in args] + [defn.sort()]
    f = z3.Function(name, *sorts)
    def_ax = axiom(z3.ForAll(args, f(*args) == defn), reason="definition")
    # assert f not in __sig or __sig[f].eq(   def_ax.thm)  # Check for redefinitions. This is kind of painful. Hmm.
    # Soft warning is more pleasant.
    if f not in __sig or __sig[f].eq(def_ax.thm):
        __sig[f] = def_ax.thm
    else:
        print("WARNING: Redefining function", f, "from", __sig[f], "to", def_ax.thm)
    return f, def_ax
