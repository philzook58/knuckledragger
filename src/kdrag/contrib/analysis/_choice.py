"""Pointwise choice for gauges and real sequences."""

import kdrag as kd
import kdrag.smt as smt
from kdrag import FreshVar, Theorem
from kdrag.smt import ArraySort, BoolSort, Const, Exists, ForAll, Lambda, Reals
from kdrag.theories.real import R, RFun
from kdrag.theories.real.rseq import a, n

D = Const("D", RFun)
x, y = Reals("x y")

# A pointwise choice of radii is a gauge function.
P = Const("P", ArraySort(R, R, BoolSort()))
_P, _x = FreshVar("P", P.sort()), FreshVar("x", R)
assert isinstance(_P, smt.ArrayRef)
(_choice,), _choice_spec = kd.kernel.obtain(Exists(y, _P[_x, y]))


@Theorem(ForAll(P, ForAll(x, Exists(y, P[x, y])), Exists(D, ForAll(x, P[x, D[x]]))))
def axiom_of_choice(l):
    P = l.fix()
    l.intro()
    l.exists(Lambda(_x, smt.substitute(_choice, (_P, P))))
    z = l.fix()
    l.auto(by=[_choice_spec.forall([_P, _x])(P, z)])


# Use the same pointwise choice rule for integer-indexed real sequences.
P_seq = Const("P", ArraySort(smt.IntSort(), R, BoolSort()))
_P_seq = FreshVar("P", P_seq.sort())
_n = FreshVar("n", smt.IntSort())
assert isinstance(_P_seq, smt.ArrayRef)
(_select_term,), _select_term_spec = kd.kernel.obtain(Exists(y, _P_seq[_n, y]))


@Theorem(
    ForAll(
        P_seq,
        ForAll(n, n >= 0, Exists(y, P_seq[n, y])),
        Exists(a, ForAll(n, n >= 0, P_seq[n, a[n]])),
    )
)
def exists_seq_of_forall_exists(l):
    P = l.fix()
    available = l.intro()
    l.exists(Lambda(_n, smt.substitute(_select_term, (_P_seq, P))))
    j = l.fix()
    nonneg = l.intro()
    l.specialize(available, j, nonneg)
    l.auto(by=[_select_term_spec.forall([_P_seq, _n])(P, j)])
