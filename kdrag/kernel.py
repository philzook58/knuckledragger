import kdrag.smt as smt
from dataclasses import dataclass
from typing import Any
import logging
from . import config

logger = logging.getLogger("knuckledragger")


@dataclass(frozen=True)
class Proof(smt.Z3PPObject):
    thm: smt.BoolRef
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
    thm: smt.BoolRef,
    by: list[Proof] = [],
    admit=False,
    timeout=1000,
    dump=False,
    solver=None,
) -> Proof:
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
        logger.warning("Admitting lemma {}".format(thm))
        return __Proof(thm, by, True)
    else:
        if solver is None:
            solver = config.solver
        s = solver()
        s.set("timeout", timeout)
        for p in by:
            if not isinstance(p, __Proof):
                raise LemmaError("In by reasons:", p, "is not a Proof object")
            s.add(p.thm)
        s.add(smt.Not(thm))
        if dump:
            print(s.sexpr())
        res = s.check()
        if res != smt.unsat:
            if res == smt.sat:
                raise LemmaError(thm, "Countermodel", s.model())
            raise LemmaError("lemma", thm, res)
        else:
            return __Proof(thm, by, False)


def axiom(thm: smt.BoolRef, by=[]) -> Proof:
    """Assert an axiom.

    Axioms are necessary and useful. But you must use great care.

    Args:
        thm: The axiom to assert.
        by: A python object explaining why the axiom should exist. Often a string explaining the axiom.
    """
    return __Proof(thm, by, admit=True)


@dataclass(frozen=True)
class Defn:
    name: str
    args: list[smt.ExprRef]
    body: smt.ExprRef
    ax: Proof


defns: dict[smt.FuncDecl, Defn] = {}
"""
defn holds definitional axioms for function symbols.
"""
smt.FuncDeclRef.defn = property(lambda self: defns[self].ax)


def define(name: str, args: list[smt.ExprRef], body: smt.ExprRef) -> smt.FuncDeclRef:
    """
    Define a non recursive definition. Useful for shorthand and abstraction. Does not currently defend against ill formed definitions.
    TODO: Check for bad circularity, record dependencies

    Args:
        name: The name of the term to define.
        args: The arguments of the term.
        defn: The definition of the term.

    Returns:
        tuple[smt.FuncDeclRef, __Proof]: A tuple of the defined term and the proof of the definition.
    """
    sorts = [arg.sort() for arg in args] + [body.sort()]
    f = smt.Function(name, *sorts)
    if len(args) > 0:
        def_ax = axiom(smt.ForAll(args, f(*args) == body), by="definition")
    else:
        def_ax = axiom(f(*args) == body, by="definition")
    # assert f not in __sig or __sig[f].eq(   def_ax.thm)  # Check for redefinitions. This is kind of painful. Hmm.
    # Soft warning is more pleasant.
    defn = Defn(name, args, body, def_ax)
    if f not in defns or defns[f].ax.thm.eq(def_ax.thm):
        defns[f] = defn
    else:
        print("WARNING: Redefining function", f, "from", defns[f].ax, "to", def_ax.thm)
        defns[f] = defn
    return f


def define_fix(name: str, args: list[smt.ExprRef], retsort, fix_lam) -> smt.FuncDeclRef:
    """
    Define a recursive definition.
    """
    sorts = [arg.sort() for arg in args]
    sorts.append(retsort)
    f = smt.Function(name, *sorts)

    # wrapper to record calls
    calls = set()

    def record_f(*args):
        calls.add(args)
        return f(*args)

    defn = define(name, args, fix_lam(record_f))
    # TODO: check for well foundedness/termination, custom induction principle.
    return defn
