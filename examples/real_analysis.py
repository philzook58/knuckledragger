"""Prove global continuity once, then derive continuity and limits at any point."""

from kdrag import FreshVars, Theorem
from kdrag.smt import ForAll, Lambda, Real, RealSort
from kdrag.theories.real import (
    abs,
    cont_at,
    cont_at_has_lim_at,
    is_cont,
    is_cont_cont_at,
)

x = Real("x")
a, p = FreshVars("a p", RealSort())


@Theorem(ForAll(a, is_cont(Lambda(x, a))))
def is_cont_constant(l):
    l.unfold(is_cont).unfold(cont_at).unfold(abs).auto()


@Theorem(is_cont(Lambda(x, x)))
def is_cont_identity(l):
    l.unfold(is_cont).unfold(cont_at).unfold(abs).auto()


@Theorem(ForAll(a, is_cont(Lambda(x, x + a))))
def is_cont_translation(l):
    l.unfold(is_cont).unfold(cont_at).unfold(abs).auto()


@Theorem(is_cont(Lambda(x, abs(x))))
def is_cont_abs(l):
    l.unfold(is_cont).unfold(cont_at).unfold(abs).auto()


# Apply the bridge lemmas directly, then generalize the arbitrary parameters.
cont_at_constant = is_cont_cont_at(Lambda(x, a), p)(is_cont_constant(a)).forall([a, p])
cont_at_identity = is_cont_cont_at(Lambda(x, x), p)(is_cont_identity).forall([p])
cont_at_translation = is_cont_cont_at(Lambda(x, x + a), p)(
    is_cont_translation(a)
).forall([a, p])
cont_at_abs = is_cont_cont_at(Lambda(x, abs(x)), p)(is_cont_abs).forall([p])

# A continuous function tends to its value at the point.
lim_at_constant = cont_at_has_lim_at(Lambda(x, a), p)(cont_at_constant(a, p)).forall(
    [a, p]
)
lim_at_identity = cont_at_has_lim_at(Lambda(x, x), p)(cont_at_identity(p)).forall([p])
lim_at_translation = cont_at_has_lim_at(Lambda(x, x + a), p)(
    cont_at_translation(a, p)
).forall([a, p])
lim_at_abs = cont_at_has_lim_at(Lambda(x, abs(x)), p)(cont_at_abs(p)).forall([p])
