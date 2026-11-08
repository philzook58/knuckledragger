"""Prove global continuity once, then derive continuity and limits at any point."""

from kdrag import FreshVars, Theorem
from kdrag.smt import ForAll, Lambda, Real, RealSort
from kdrag.theories.real import (
    abs,
    fadd,
    fmul,
    cont_at,
    cont_at_of_is_cont,
    has_lim_at_of_cont_at,
    is_cont,
    is_cont_add,
    is_cont_mul,
)

x = Real("x")
a, p = FreshVars("a p", RealSort())


@Theorem(ForAll(a, is_cont(Lambda(x, a))))
def continuous_const(l):
    l.unfold(is_cont).unfold(cont_at).unfold(abs).auto()


@Theorem(is_cont(Lambda(x, x)))
def continuous_id(l):
    l.unfold(is_cont).unfold(cont_at).unfold(abs).auto()


@Theorem(ForAll(a, is_cont(Lambda(x, x + a))))
def continuous_add_const(l):
    a = l.fix()
    identity, constant = Lambda(x, x), Lambda(x, a)
    l.auto(
        by=[
            fadd.defn(identity, constant),
            is_cont_add(identity, constant)(continuous_id, continuous_const(a)),
        ]
    )


@Theorem(is_cont(Lambda(x, x * x)))
def continuous_sq(l):
    identity = Lambda(x, x)
    l.auto(
        by=[
            fmul.defn(identity, identity),
            is_cont_mul(identity, identity)(continuous_id, continuous_id),
        ]
    )


@Theorem(is_cont(Lambda(x, abs(x))))
def continuous_abs(l):
    l.unfold(is_cont).unfold(cont_at).unfold(abs).auto()


# Apply the bridge lemmas directly, then generalize the arbitrary parameters.
continuous_at_const = cont_at_of_is_cont(Lambda(x, a), p)(continuous_const(a)).forall(
    [a, p]
)
continuous_at_id = cont_at_of_is_cont(Lambda(x, x), p)(continuous_id).forall([p])
continuous_at_add_const = cont_at_of_is_cont(Lambda(x, x + a), p)(
    continuous_add_const(a)
).forall([a, p])
continuous_at_sq = cont_at_of_is_cont(Lambda(x, x * x), p)(continuous_sq).forall([p])
continuous_at_abs = cont_at_of_is_cont(Lambda(x, abs(x)), p)(continuous_abs).forall([p])

# A continuous function tends to its value at the point.
has_lim_at_const = has_lim_at_of_cont_at(Lambda(x, a), p)(
    continuous_at_const(a, p)
).forall([a, p])
has_lim_at_id = has_lim_at_of_cont_at(Lambda(x, x), p)(continuous_at_id(p)).forall([p])
has_lim_at_add_const = has_lim_at_of_cont_at(Lambda(x, x + a), p)(
    continuous_at_add_const(a, p)
).forall([a, p])
has_lim_at_sq = has_lim_at_of_cont_at(Lambda(x, x * x), p)(continuous_at_sq(p)).forall(
    [p]
)
has_lim_at_abs = has_lim_at_of_cont_at(Lambda(x, abs(x)), p)(
    continuous_at_abs(p)
).forall([p])
