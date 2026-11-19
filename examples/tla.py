from kdrag.all import *
from kdrag import Theorem
from kdrag.smt import And, ArraySort, Const, ForAll, FreshInt, IntSort, Lambda
import kdrag.modal as mod


TInt = ArraySort(IntSort(), IntSort())
hr = Const("hr", TInt)


def Next(x):
    t = FreshInt(prefix="t")
    return Lambda([t], x(t + 1))


def Always(x, unchanged=None):
    t1 = FreshInt(prefix="t")
    t2 = FreshInt(prefix="t")
    if unchanged is not None:
        return Lambda([t1], ForAll([t2], t2 >= t1, (x(t2) | UNCHANGED(*unchanged)(t2))))
    else:
        return Lambda([t1], ForAll([t2], t2 >= t1, x(t2)))


def Valid(x):
    return x(0)


def UNCHANGED(*args):
    t = FreshInt(prefix="t")
    return Lambda([t], And(*(arg(t + 1) == arg(t) for arg in args)))


HCini = (0 <= hr) & (hr <= 12)
HCtrans = mod.PEq(Next(hr), mod.PIf(hr < 12, hr + 1, 0))  # todo stutter


@Theorem(Valid(mod.PImplies(HCini & Always(HCtrans), Always(HCini))))
def clock_inv(l):
    l.intro()
    _t = l.fix()
    l.induct(_t)
    l.auto()  # neg t
    l.auto()  # 0
    l.auto()  # pos t


clock_inv

UNCHANGED(hr, hr)
Always(HCtrans, unchanged=[hr])


def _test():
    """
    >>> True
    True
    """
