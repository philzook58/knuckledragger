import z3
from dataclasses import dataclass
from typing import Any
import logging

logger = logging.getLogger("knuckeldragger")


@dataclass(frozen=True)
class Proof(z3.Z3PPObject):
    thm: z3.BoolRef
    reason: list[Any]
    admit: bool

    def _repr_html_(self):
        return "&#8870;" + repr(self.thm)

    def __repr__(self):
        return "|- " + repr(self.thm)


# It is unlikely that users should be accessing the `Proof` constructor directly.
# This is not ironclad. If you really want the Proof constructor, I can't stop you.
__Proof = Proof
Proof = None


def is_proof(p):
    return isinstance(p, __Proof)


class LemmaError(Exception):
    pass


def lemma(
    thm: z3.BoolRef, by: list[Proof] = [], admit=False, timeout=1000, dump=False
) -> Proof:
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
        logger.warn("Admitting lemma {}".format(thm))
        return __Proof(thm, by, True)
    else:
        s = z3.Solver()
        s.set("timeout", timeout)
        for n, p in enumerate(by):
            if not isinstance(p, __Proof):
                raise LemmaError("In by reasons:", p, "is not a Proof object")
            s.assert_and_track(p.thm, "by_{}".format(n))
        s.assert_and_track(z3.Not(thm), "knuckledragger_goal")
        if dump:
            print(s.sexpr())
        res = s.check()
        if res != z3.unsat:
            if res == z3.sat:
                raise LemmaError(thm, "Countermodel", s.model())
            raise LemmaError("lemma", thm, res)
        else:
            core = s.unsat_core()
            assert z3.Bool("knuckledragger_goal") in core
            if len(core) < len(by) + 1:
                print("WARNING: Unneeded assumptions. Used", core)
            return __Proof(thm, by, False)


def axiom(thm: z3.BoolRef, by=[]) -> Proof:
    """Assert an axiom.

    Axioms are necessary and useful. But you must use great care.

    Args:
        thm: The axiom to assert.
        by: A python object explaining why the axiom should exist. Often a string explaining the axiom.
    """
    return __Proof(thm, by, admit=True)


defn: dict[z3.FuncDecl, Proof] = {}
"""
defn holds definitional axioms for function symbols.
"""
z3.FuncDeclRef.defn = property(lambda self: defn[self])


def define(
    name: str, args: list[z3.ExprRef], defn_expr: z3.ExprRef
) -> tuple[z3.FuncDeclRef, __Proof]:
    """Define a non recursive definition. Useful for shorthand and abstraction.

    Args:
        name: The name of the term to define.
        args: The arguments of the term.
        defn: The definition of the term.

    Returns:
        tuple[z3.FuncDeclRef, __Proof]: A tuple of the defined term and the proof of the definition.
    """
    sorts = [arg.sort() for arg in args] + [defn_expr.sort()]
    f = z3.Function(name, *sorts)
    if len(args) > 0:
        def_ax = axiom(z3.ForAll(args, f(*args) == defn_expr), by="definition")
    else:
        def_ax = axiom(f(*args) == defn_expr, by="definition")
    # assert f not in __sig or __sig[f].eq(   def_ax.thm)  # Check for redefinitions. This is kind of painful. Hmm.
    # Soft warning is more pleasant.
    if f not in defn or defn[f].thm.eq(def_ax.thm):
        defn[f] = def_ax
    else:
        print("WARNING: Redefining function", f, "from", defn[f], "to", def_ax.thm)
        defn[f] = def_ax
    return f
