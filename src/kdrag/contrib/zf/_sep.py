"""A local helper for sets defined by separation in contrib.zf."""

import kdrag as kd
from kdrag.smt import And, ExprRef, ForAll, Lambda
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import elem, sep


def define_sep(name: str, args: list[ExprRef], A: ExprRef, x: ExprRef, P):
    """Define S(args) = {x ∈ A | P} and prove its membership lemma

        ∀ args x. x ∈ S(args) == (x ∈ A ∧ P).

    Returns the definition and the lemma. Naming the set and stating membership
    once avoids a lambda inside `sep` in later proofs, which is seed-fragile."""
    S = kd.define(name, args, sep(A, Lambda(x, P)))
    l = kd.Lemma(ForAll(args + [x], elem(x, S(*args)) == And(elem(x, A), P)))
    l.fixes()
    l.unfold(S)
    l.rw(zf.elem_sep)
    l.simp()
    l.auto()
    return S, l.qed()
