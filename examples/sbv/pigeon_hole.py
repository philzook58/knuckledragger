"""If a finite integer list sums to more than its length, some entry exceeds 1.

Adapted from Levent Erkok's SBV example Documentation/SBV/Examples/TP/PigeonHole.hs:
https://github.com/LeventErkok/sbv/blob/0e9b17044cbdbf0d2395a43d0de37aaddf9be84b/Documentation/SBV/Examples/TP/PigeonHole.hs
Copyright (c) Levent Erkok. Distributed under BSD-3-Clause; see LICENSE here.

Run from the repository root: PYTHONPATH=src python examples/sbv/pigeon_hole.py
"""

from kdrag import Theorem, prove
from kdrag.smt import (
    And,
    ArraySort,
    Bool,
    BoolSort,
    Const,
    Consts,
    Empty,
    ForAll,
    Ints,
    IntSort,
    Lambda,
    Length,
    Implies,
    Or,
    SeqFoldLeft,
    SeqRef,
    SeqSort,
    ArithRef,
    BoolRef,
)
from kdrag.rewrite import beta
from kdrag.tactics import ProofState

Z = IntSort()
List = SeqSort(Z)
xs = Const("xs", List)
x, a = Ints("x a")
b = Bool("b")
add = Lambda([a, x], a + x)
any_step = Lambda([b, x], Or(b, x > 1))


def list_sum(xs: SeqRef) -> ArithRef:
    return SeqFoldLeft(add, 0, xs)


def overflow(xs: SeqRef) -> BoolRef:
    return SeqFoldLeft(any_step, False, xs)


# Prove the higher-order principle once, with the predicate kept abstract.
P = Const("P", ArraySort(List, BoolSort()))
prefix, suffix, target = Consts("prefix suffix target", List)
last = Const("last", Z)
snoc_step = ForAll([prefix, last], P[prefix], P[prefix + [last]])


@Theorem(
    ForAll(
        [P, suffix],
        snoc_step,
        ForAll([prefix], P[prefix], P[prefix + suffix]),
    )
)
def snoc_append_preserves(pf: ProofState):
    """Closure under snoc implies closure under appending any suffix."""
    P, suffix = pf.fixes()
    step = pf.intro()
    pf.induct(suffix)
    pf.auto()
    last, suffix = pf.fixes()
    ih = pf.intro()
    prefix = pf.fix()
    premise = pf.intro()
    next_premise = pf.specialize(step, prefix, last, premise)
    pf.specialize(ih, prefix + [last], next_premise)
    pf.auto()


@Theorem(
    ForAll(
        [P, target],
        Implies(And(P[Empty(List)], snoc_step), P[target]),
    )
)
def snoc_induction(pf: ProofState):
    """The higher-order empty/snoc principle, derived from cons induction."""
    P, target = pf.fixes()
    pf.intro()
    pf.split(at=0)
    base, step = pf.ctx
    pf.specialize(snoc_append_preserves, P, target, step, Empty(List), base)
    pf.auto()


def induct_snoc(xs: SeqRef, P):
    """Instantiate the proved snoc principle for these integer sequences."""
    instance = snoc_induction(Lambda([prefix], P(prefix)), xs)
    return prove(beta(instance.thm), by=[instance])


@Theorem(
    ForAll(
        [xs],
        ForAll(
            [a, b],
            And(
                SeqFoldLeft(add, a, xs) == a + list_sum(xs),
                SeqFoldLeft(any_step, b, xs) == Or(b, overflow(xs)),
            ),
        ),
    )
)
def fold_accumulators(pf: ProofState):
    """Cons unfolding changes the initial accumulator; generalize it first."""
    xs = pf.fix()
    pf.induct(xs)
    pf.auto()
    x, xs = pf.fixes()
    ih = pf.intro()
    a, b = pf.fixes()
    pf.specialize(ih, a + x, Or(b, x > 1), keep=True)
    pf.specialize(ih, x, x > 1)
    pf.auto()


@Theorem(ForAll([xs], list_sum(xs) > Length(xs), overflow(xs)))
def pigeon_hole_cons(pf: ProofState):
    """Use cons unfolding plus the generalized accumulator equations."""
    xs = pf.fix()
    pf.induct(xs)
    pf.auto()
    x, xs = pf.fixes()
    pf.intros()
    pf.auto(by=[fold_accumulators(xs, x, x > 1)])


@Theorem(ForAll([xs], list_sum(xs) > Length(xs), overflow(xs)))
def pigeon_hole_snoc(pf: ProofState):
    """Snoc unfolding exposes the final addition and disjunction directly."""
    xs = pf.fix()
    pf.induct(xs, using=induct_snoc)
    pf.auto()
    xs, x = pf.fixes()
    pf.intros()
    pf.auto()


if __name__ == "__main__":
    print(pigeon_hole_cons)
    print(pigeon_hole_snoc)
