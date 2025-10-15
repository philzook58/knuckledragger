"""
Known Bits Abstract Domain

https://pypy.org/posts/2024/08/toy-knownbits.html
https://arxiv.org/pdf/2105.05398 Sound, Precise, and Fast Abstract Interpretation with Tristate Numbers
"""

import kdrag as kd
import kdrag.smt as smt

W = 8
KnownBits = kd.Struct(
    "KnownBits", ("ones", smt.BitVecSort(W)), ("unknowns", smt.BitVecSort(W))
)
x, y, z = smt.Consts("x y z", KnownBits)
a, b, c = smt.Consts("a b c", smt.BitVecSort(W))

setof = kd.define(
    "setof",
    [x],
    smt.Lambda([a], (~x.unknowns & a) == x.ones),
)
kd.notation.getitem.register(KnownBits, lambda a, idx: setof(a)[idx])

kd.prove(KnownBits.mk(0, 0)[0], unfold=1)

wf = kd.notation.wf.define([x], x.ones & x.unknowns == 0)

const = kd.define("const", [a], KnownBits.mk(a, 0))
is_const = kd.define("is_const", [x], x.unknowns == 0)

kd.prove(
    kd.QForAll([x], is_const(x), smt.Exists([a], kd.QForAll([b], x[b], a == b))),
    unfold=1,
)


def Knowns(x):
    return ~x.unknowns


def Zeros(x):
    return ~x.unknowns & ~x.ones


zeros = kd.define("zeros", [x], Zeros(x))

invert = kd.notation.invert.define([x], KnownBits.mk(Zeros(x), x.unknowns))


def test():
    """
    >>> True
    True
    """
