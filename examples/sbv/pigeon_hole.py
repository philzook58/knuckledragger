"""If a finite integer list sums to more than its length, some entry exceeds 1.

Adapted from Levent Erkok's SBV example Documentation/SBV/Examples/TP/PigeonHole.hs:
https://github.com/LeventErkok/sbv/blob/0e9b17044cbdbf0d2395a43d0de37aaddf9be84b/Documentation/SBV/Examples/TP/PigeonHole.hs
Copyright (c) Levent Erkok. Distributed under BSD-3-Clause; see LICENSE here.

Run from the repository root: PYTHONPATH=src python examples/sbv/pigeon_hole.py
"""

from kdrag import Tail, Theorem, define
from kdrag.smt import (
    BoolSort,
    Const,
    Empty,
    ForAll,
    Function,
    If,
    IntSort,
    Length,
    Or,
    SeqSort,
)
from kdrag.tactics import ProofState

Z = IntSort()
List = SeqSort(Z)
xs = Const("xs", List)
nil = Empty(List)

# SBV supplies these through its sum and any list combinators.
list_sum = Function("SBV.PigeonHole.sum", List, Z)
list_sum = define(
    "SBV.PigeonHole.sum",
    xs,
    If(xs == nil, 0, xs[0] + list_sum(Tail(xs))),
)
overflow = Function("SBV.PigeonHole.overflow", List, BoolSort())
overflow = define(
    "SBV.PigeonHole.overflow",
    xs,
    If(xs == nil, False, Or(xs[0] > 1, overflow(Tail(xs)))),
)


@Theorem(ForAll([xs], list_sum(xs) > Length(xs), overflow(xs)))
def pigeon_hole(pf: ProofState):
    """If the head is at most 1, the tail must still sum to more than its length."""
    xs = pf.fix()
    pf.induct(xs)
    pf.auto(by=[list_sum.defn, overflow.defn])
    x, xs = pf.fixes()
    pf.intros()
    whole = [x] + xs
    # Linear arithmetic supplies the tail premise needed by the IH.
    pf.auto(by=[list_sum.defn(whole), overflow.defn(whole)])


if __name__ == "__main__":
    print(pigeon_hole)
