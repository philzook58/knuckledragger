"""Accumulator reverse agrees with ordinary reverse on arbitrary finite lists.

Adapted from Levent Erkok's SBV example Documentation/SBV/Examples/TP/RevAcc.hs:
https://github.com/LeventErkok/sbv/blob/0e9b17044cbdbf0d2395a43d0de37aaddf9be84b/Documentation/SBV/Examples/TP/RevAcc.hs
Copyright (c) Levent Erkok. Distributed under BSD-3-Clause; see LICENSE here.

Run from the repository root: PYTHONPATH=src python examples/sbv/rev_acc.py
"""

from kdrag import Tail, Theorem, define, prove
from kdrag.smt import (
    Consts,
    DeclareSort,
    Empty,
    ForAll,
    Function,
    If,
    SeqSort,
)
from kdrag.tactics import ProofState

# No assumptions about elements: use the SMT theory of finite sequences.
Element = DeclareSort("SBV.RevAcc.Element")
List = SeqSort(Element)
nil = Empty(List)
xs, acc = Consts("xs acc", List)

reverse = Function("SBV.RevAcc.reverse", List, List)
reverse = define(
    "SBV.RevAcc.reverse",
    xs,
    If(xs == nil, nil, reverse(Tail(xs)) + [xs[0]]),
)
rev_acc = Function("SBV.RevAcc.rev_acc", List, List, List)
rev_acc = define(
    "SBV.RevAcc.rev_acc",
    [acc, xs],
    If(xs == nil, acc, rev_acc([xs[0]] + acc, Tail(xs))),
)


@Theorem(ForAll([xs], ForAll([acc], rev_acc(acc, xs) == reverse(xs) + acc)))
def rev_acc_correct(pf: ProofState):
    """Keep the accumulator general so the induction hypothesis can change it."""
    xs = pf.fix()
    # The induction predicate still contains forall acc.
    pf.induct(xs)
    pf.auto(by=[rev_acc.defn, reverse.defn])

    x, xs = pf.fixes()
    pf.intro()
    acc = pf.fix()
    # eq advances the RHS; swap sides to follow SBV's calculation forwards.
    pf.symm()
    pf.eq(rev_acc([x] + acc, xs), by=[rev_acc.defn])
    pf.eq(reverse(xs) + ([x] + acc))  # IH at the new accumulator
    pf.eq((reverse(xs) + [x]) + acc)  # append associativity
    pf.eq(reverse([x] + xs) + acc, by=[reverse.defn])
    pf.auto()


rev_correct = prove(ForAll([xs], rev_acc(nil, xs) == reverse(xs)), by=[rev_acc_correct])


if __name__ == "__main__":
    print(rev_correct)
