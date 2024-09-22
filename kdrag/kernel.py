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
    admit: bool = False

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


def consider(x: smt.ExprRef) -> Proof:
    """
    Axiom schema. We may give a fresh name to any constant. An "anonymous" form of define.
    The purpose of this is to seed the solver with interesting terms.
    Pointing out the interesting terms is sometimes the essence of a proof.
    """
    return axiom(smt.FreshConst(x.sort(), prefix="consider") == x)


def fresh_const(q: smt.QuantifierRef):
    return [
        smt.FreshConst(q.var_sort(i), prefix=q.var_name(i)) for i in range(q.num_vars())
    ]


def instan(ts: list[smt.ExprRef], pf: Proof) -> Proof:
    """
    Instantiate a universally quantified formula.
    This is forall elimination
    """
    assert is_proof(pf) and pf.thm.is_forall()

    return __Proof(smt.substitute_vars(pf.thm.body(), *reversed(ts)), reason=[pf])


def forget(ts: list[smt.ExprRef], pf: Proof) -> Proof:
    """
    "Forget" a term using existentials. This is existential introduction.
    """
    assert is_proof(pf)
    vs = fresh_const(pf.thm)
    return __Proof(smt.Exists(vs, smt.substitute(pf.thm, *zip(ts, vs))), reason=[pf])


def skolem(pf: Proof) -> tuple[list[smt.ExprRef], Proof]:
    """
    Skolemize an existential quantifier.
    """
    assert is_proof(pf) and pf.thm.is_exists()

    skolems = fresh_const(pf.thm)
    return skolems, __Proof(
        smt.substitute_vars(pf.thm.body(), *reversed(skolems)), reason=[pf]
    )


def herb(thm: smt.QuantifierRef) -> tuple[list[smt.ExprRef], Proof]:
    """
    Herbrandize a theorem.
    It is sufficient to prove a theorem for fresh consts to prove a universal.
    Note: Perhaps lambdaized form is better?
    """
    assert thm.is_forall()
    herbs = fresh_const(thm)
    return herbs, __Proof(smt.Implies(smt.substitute_vars(thm, *reversed(herbs)), thm))
