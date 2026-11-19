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
    Empty,
    ForAll,
    FreshConst,
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
from kdrag.tactics import Lemma, ProofState

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


def induct_snoc(xs: SeqRef, P):
    """Derive empty/snoc induction from cons induction, without a new axiom."""
    sort = xs.sort()
    predicate = FreshConst(ArraySort(sort, BoolSort()))
    prefix, suffix, target = FreshConst(sort), FreshConst(sort), FreshConst(sort)
    last = FreshConst(sort.basis())
    empty = Empty(sort)
    step = ForAll([prefix, last], predicate[prefix], predicate[prefix + [last]])

    # Keep the predicate abstract while deriving the principle. Expanding the
    # fold-based predicate here makes quantifier instantiation much harder.
    extension = Lemma(
        ForAll(
            [predicate, suffix],
            step,
            ForAll([prefix], predicate[prefix], predicate[prefix + suffix]),
        )
    )
    predicate1, suffix1 = extension.fixes()
    step1 = extension.intro()
    extension.induct(suffix1)
    extension.auto()
    last1, suffix1 = extension.fixes()
    ih = extension.intro()
    prefix1 = extension.fix()
    premise = extension.intro()
    next_premise = extension.specialize(step1, prefix1, last1, premise)
    extension.specialize(ih, prefix1 + [last1], next_premise)
    extension.auto()
    append_preserves = extension.qed()

    pf = Lemma(ForAll([predicate, target], predicate[empty], step, predicate[target]))
    predicate1, target1 = pf.fixes()
    base, step1 = pf.intros()
    pf.specialize(append_preserves, predicate1, target1, step1, empty, base)
    pf.auto()
    schema = pf.qed()
    instance = schema(Lambda([prefix], P(prefix)), xs)
    return prove(
        Implies(
            And(P(empty), ForAll([prefix, last], P(prefix), P(prefix + [last]))), P(xs)
        ),
        by=[instance],
    )


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
