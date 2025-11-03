from kdrag.all import *
import kdrag.modal as mod


TInt = smt.ArraySort(smt.IntSort(), smt.IntSort())
hr = smt.Const("hr", TInt)


def Next(x):
    t = smt.FreshInt(prefix="t")
    return smt.Lambda([t], x(t + 1))


def Always(x, unchanged=None):
    t1 = smt.FreshInt(prefix="t")
    t2 = smt.FreshInt(prefix="t")
    if unchanged is not None:
        return smt.Lambda(
            [t1], smt.ForAll([t2], t2 >= t1, (x(t2) | UNCHANGED(*unchanged)(t2)))
        )
    else:
        return smt.Lambda([t1], smt.ForAll([t2], t2 >= t1, x(t2)))


def Valid(x):
    return x(0)


def UNCHANGED(*args):
    t = smt.FreshInt(prefix="t")
    return smt.Lambda([t], smt.And(*(arg(t + 1) == arg(t) for arg in args)))


HCini = (0 <= hr) & (hr <= 12)
HCtrans = mod.PEq(Next(hr), mod.PIf(hr < 12, hr + 1, 0))  # todo stutter


@kd.Theorem(Valid(mod.PImplies(HCini & Always(HCtrans), Always(HCini))))
def clock_inv(l):
    l.intros()
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
