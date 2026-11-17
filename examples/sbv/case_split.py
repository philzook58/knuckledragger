"""Prove that 2*n*n + n + 1 is never divisible by 3, for every integer n.

Adapted from Levent Erkok's SBV example Documentation/SBV/Examples/TP/CaseSplit.hs:
https://github.com/LeventErkok/sbv/blob/0e9b17044cbdbf0d2395a43d0de37aaddf9be84b/Documentation/SBV/Examples/TP/CaseSplit.hs
Copyright (c) Levent Erkok. Distributed under BSD-3-Clause; see LICENSE here.

Run from the repository root: PYTHONPATH=src python examples/sbv/case_split.py
"""

from kdrag import Theorem
from kdrag.smt import ForAll, Int
from kdrag.tactics import ProofState

n = Int("n")


@Theorem(ForAll([n], (2 * n * n + n + 1) % 3 != 0))
def not_div3(pf: ProofState) -> None:
    """Split on the three possible Euclidean remainders, including negative n."""
    n = pf.fix()
    pf.cases(n % 3 == 0, n % 3 == 1, n % 3 == 2, timeout=100)
    # Each branch fixes the remainder; Z3 can now finish the arithmetic.
    for _ in range(3):
        pf.auto(timeout=100)


if __name__ == "__main__":
    print(not_div3)
