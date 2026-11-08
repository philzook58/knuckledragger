"""Short continuity and limit proofs using definitions and Z3."""

from kdrag import Theorem, prove
from kdrag.smt import ForAll, Lambda, Reals
from kdrag.theories.real import abs, cont_at, has_lim_at

x, a, p = Reals("x a p")

cont_at_constant = prove(
    ForAll([a, p], cont_at(Lambda(x, a), p)),
    by=[abs.defn, cont_at.defn],
)

cont_at_translation = prove(
    ForAll(a, cont_at(Lambda(x, x + a), 0)),
    by=[abs.defn, cont_at.defn],
)


# For nested absolute values, give the epsilon-delta witness explicitly.
@Theorem(cont_at(Lambda(x, abs(x)), 0))
def cont_at_abs_zero(l):
    l.unfold(cont_at)
    eps = l.fix()
    l.intros()
    l.exists(eps)
    l.unfold(abs).auto()


lim_at_constant = prove(
    ForAll([a, p], has_lim_at(Lambda(x, a), p, a)),
    by=[abs.defn, has_lim_at.defn],
)

lim_at_identity = prove(
    has_lim_at(Lambda(x, x), 0, 0),
    by=[abs.defn, has_lim_at.defn],
)

lim_at_translation = prove(
    ForAll(a, has_lim_at(Lambda(x, x + a), 0, a)),
    by=[abs.defn, has_lim_at.defn],
)


@Theorem(has_lim_at(Lambda(x, abs(x)), 0, 0))
def lim_at_abs_zero(l):
    l.unfold(has_lim_at)
    eps = l.fix()
    l.intros()
    l.exists(eps)
    l.unfold(abs).auto()
