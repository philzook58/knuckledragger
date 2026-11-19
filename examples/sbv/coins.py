"""Make every amount >= 8 using 3- and 5-unit coins.

Adapted from Levent Erkok's SBV example Documentation/SBV/Examples/TP/Coins.hs:
https://github.com/LeventErkok/sbv/blob/0e9b17044cbdbf0d2395a43d0de37aaddf9be84b/Documentation/SBV/Examples/TP/Coins.hs
Copyright (c) Levent Erkok. Distributed under BSD-3-Clause; see LICENSE here.

Run from the repository root: PYTHONPATH=src python examples/sbv/coins.py
"""

from kdrag import OptionSort, Struct, Theorem, cond, define
from kdrag.smt import Const, ForAll, Function, If, Int, IntSort
from kdrag.tactics import ProofState
from kdrag.theories.int import induct_strong

Z = IntSort()
Pocket = Struct("SBV.Coins.Pocket", ("num3s", Z), ("num5s", Z))
Change = OptionSort(Pocket)
n = Int("n")
pocket = Const("pocket", Change)

mk_change = Function("SBV.Coins.mk_change", Z, Change)
previous = mk_change(n - 3)
mk_change = define(
    "SBV.Coins.mk_change",
    n,
    cond(
        (n < 8, Change.None_),
        (n == 8, Change.Some(Pocket(1, 1))),
        (n == 9, Change.Some(Pocket(3, 0))),
        (n == 10, Change.Some(Pocket(0, 2))),
        default=If(
            previous.is_None_,
            Change.None_,
            Change.Some(Pocket(previous.val.num3s + 1, previous.val.num5s)),
        ),
    ),
)

eval_pocket = define(
    "SBV.Coins.eval_pocket",
    pocket,
    If(pocket.is_None_, 0, 3 * pocket.val.num3s + 5 * pocket.val.num5s),
)


@Theorem(ForAll([n], n >= 8, eval_pocket(mk_change(n)) == n))
def mk_change_correct(pf: ProofState):
    """Three consecutive base amounts let the recursive case subtract 3."""
    n = pf.fix()
    pf.induct(n, using=induct_strong)
    k = pf.fix()
    ih, _ = pf.intros()  # IH at smaller absolute values, k >= 8
    pf.cases(k == 8, k == 9, k == 10, k > 10)
    pf.auto(by=[mk_change.defn(k), eval_pocket.defn])
    pf.auto(by=[mk_change.defn(k), eval_pocket.defn])
    pf.auto(by=[mk_change.defn(k), eval_pocket.defn])
    pf.specialize(ih, k - 3)
    # Its value is k-3 >= 8, so the preceding result cannot be None.
    pf.auto(by=[mk_change.defn(k), eval_pocket.defn])


if __name__ == "__main__":
    print(mk_change_correct)
