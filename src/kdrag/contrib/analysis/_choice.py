"""Pointwise choice used to construct gauges."""

import kdrag as kd
import kdrag.smt as smt
from kdrag import FreshVar, Theorem
from kdrag.smt import ArraySort, BoolSort, Const, Exists, ForAll, Lambda, Reals
from kdrag.theories.real import R, RFun

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
