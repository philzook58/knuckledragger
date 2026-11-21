"""Ackermann via two checked integer recursions, without a lexicographic measure.

Run: PYTHONPATH=src python examples/recursion/ackermann.py
The usual Ackermann equations hold for nonnegative inputs. For totality over
integers, both zero tests are extended to <= 0.
"""

from kdrag import Theorem, prove
from kdrag.tactics import ProofState
from kdrag.smt import ArraySort, Const, ForAll, Function, If, IntSort, Ints, Lambda
from kdrag.termination import define_rec

Z = IntSort()
ZtoZ = ArraySort(Z, Z)
m, n = Ints("ack_m ack_n")
g = Const("ack_g", ZtoZ)

# Given the preceding row g, construct the current row by recursion on n.
row = Function("Ackermann.row", Z, ZtoZ, Z)
define_rec(row, [n, g], If(n <= 0, g[1], g[row(n - 1, g)]))

# A(m) is the function n -> ackermann(m, n). Only m decreases here.
A = Function("Ackermann.A", Z, ZtoZ)
define_rec(A, m, If(m <= 0, Lambda([n], n + 1), Lambda([n], row(n, A(m - 1)))))

# Derive the familiar equations from the two definitions, rather than assuming them.
ack_zero = prove(ForAll([n], A(0)[n] == n + 1), by=[A.defn(0)])


@Theorem(ForAll([m], m >= 0, A(m + 1)[0] == A(m)[1]))
def ack_succ_zero(pf: ProofState):
    m = pf.fix()
    pf.intros()
    pf.auto(by=[A.defn(m + 1), row.defn(0, A(m))])


@Theorem(ForAll([m, n], m >= 0, n >= 0, A(m + 1)[n + 1] == A(m)[A(m + 1)[n]]))
def ack_succ_succ(pf: ProofState):
    m, n = pf.fixes()
    pf.intros()
    pf.intros()
    pf.auto(by=[A.defn(m + 1), row.defn(n + 1, A(m))])


if __name__ == "__main__":
    print(ack_zero)
    print(ack_succ_zero)
    print(ack_succ_succ)
