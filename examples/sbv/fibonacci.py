"""Tail-recursive Fibonacci agrees with the textbook recurrence for n >= 0.

Adapted from Levent Erkok's SBV example Documentation/SBV/Examples/TP/Fibonacci.hs:
https://github.com/LeventErkok/sbv/blob/0e9b17044cbdbf0d2395a43d0de37aaddf9be84b/Documentation/SBV/Examples/TP/Fibonacci.hs
Copyright (c) Levent Erkok. Distributed under BSD-3-Clause; see LICENSE here.

Run from the repository root: PYTHONPATH=src python examples/sbv/fibonacci.py
"""

from kdrag import Theorem, define
from kdrag.smt import ForAll, Function, If, IntSort, Ints
from kdrag.tactics import ProofState

n, k, a, b = Ints("n k a b")
Z = IntSort()

# SBV uses the convention fibonacci(0) = fibonacci(1) = 1.
fibonacci = Function("SBV.Fibonacci.fibonacci", Z, Z)
fibonacci = define(
    "SBV.Fibonacci.fibonacci",
    n,
    If(n <= 1, 1, fibonacci(n - 1) + fibonacci(n - 2)),
)
fib = Function("SBV.Fibonacci.fib", Z, Z, Z, Z)
fib = define("SBV.Fibonacci.fib", [a, b, n], If(n <= 0, a, fib(b, a + b, n - 1)))
fib_tail = define("SBV.Fibonacci.fib_tail", n, fib(1, 1, n))


@Theorem(
    ForAll(
        [n],
        ForAll(
            [k],
            n >= 0,
            k >= 0,
            fib(fibonacci(k), fibonacci(k + 1), n) == fibonacci(k + n),
        ),
    )
)
def fib_shift(pf: ProofState):
    """Consecutive Fibonacci accumulators advance by n positions."""
    n = pf.fix()
    # Keep k quantified: the recursive call shifts it to k + 1.
    pf.induct(n)
    pf.auto()  # The downward integer-induction case is vacuous.
    pf.auto(by=[fib.defn])

    n = pf.fix()
    pf.intros()
    pf.intros()
    k = pf.fix()
    pf.intros()
    pf.intros()
    pf.symm()
    pf.eq(fib(fibonacci(k + 1), fibonacci(k) + fibonacci(k + 1), n), by=[fib.defn])
    pf.eq(fib(fibonacci(k + 1), fibonacci(k + 2), n), by=[fibonacci.defn(k + 2)])
    pf.eq(fibonacci(k + 1 + n))  # IH at the shifted index k + 1.
    pf.auto()


@Theorem(ForAll([n], n >= 0, fibonacci(n) == fib_tail(n)))
def fib_correct(pf: ProofState):
    """Start the shifted invariant at k = 0, with accumulators 1 and 1."""
    n = pf.fix()
    pf.intros()
    pf.auto(
        by=[fib_shift(n, 0), fibonacci.defn(0), fibonacci.defn(1), fib_tail.defn(n)]
    )


if __name__ == "__main__":
    print(fib_correct)
