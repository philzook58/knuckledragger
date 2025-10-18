"""
Known Bits Abstract Domain

https://pypy.org/posts/2024/08/toy-knownbits.html
https://arxiv.org/pdf/2105.05398 Sound, Precise, and Fast Abstract Interpretation with Tristate Numbers
"""

import kdrag as kd
import kdrag.smt as smt
import functools


def Knowns(x):
    return ~x.unknowns


def Zeros(x):
    return ~x.unknowns & ~x.ones


def Concat(a, b):
    """
    >>> a = KB1.const(1) # 1
    >>> b = KB1.const(0) # 0
    >>> Concat(a, b)
    KnownBits_2(Concat(ones(const(1)), ones(const(0))),
            Concat(unknowns(const(1)), unknowns(const(0))))
    """
    sa = a.ones.size()
    sb = b.ones.size()
    return KB(sa + sb).T.mk(
        smt.Concat(a.ones, b.ones), smt.Concat(a.unknowns, b.unknowns)
    )


class KnownBits:
    def __init__(self, W):
        self.W = W
        KnownBits = kd.Struct(
            f"KnownBits_{W}",
            ("ones", smt.BitVecSort(W)),
            ("unknowns", smt.BitVecSort(W)),
        )
        self.T = KnownBits
        x, y, z = smt.Consts("x y z", KnownBits)
        a, b, c = smt.Consts("a b c", smt.BitVecSort(W))

        setof = kd.define(
            "setof",
            [x],
            smt.Lambda([a], (~x.unknowns & a) == x.ones),
        )
        self.setof = setof
        self.getitem = kd.notation.getitem.register(
            KnownBits, lambda a, idx: setof(a)[idx]
        )

        kd.prove(KnownBits.mk(0, 0)[0], unfold=1)

        self.wf = kd.notation.wf.define([x], (x.ones & x.unknowns) == 0)

        const = kd.define("const", [a], KnownBits.mk(a, 0))
        self.const = const
        is_const = kd.define("is_const", [x], x.unknowns == 0)
        self.is_const = is_const

        self.set_const = kd.prove(smt.ForAll([a], const(a)[a]), unfold=1)

        self.is_const_unique = kd.prove(
            kd.QForAll(
                [x], is_const(x), smt.Exists([a], kd.QForAll([b], x[b], a == b))
            ),
            unfold=1,
        )

        top = KnownBits.mk(0, -1)
        self.set_top = kd.prove(smt.ForAll([a], top[a]), unfold=1)

        zeros = kd.define("zeros", [x], Zeros(x))
        self.zeros = zeros

        invert = kd.notation.invert.define([x], KnownBits.mk(Zeros(x), x.unknowns))
        self.invert = invert

        self.invert_const = kd.prove(smt.ForAll([a], ~const(a) == const(~a)), unfold=1)
        self.invert_top = kd.prove(~top == top, unfold=1)
        self.invert_invol = kd.prove(kd.QForAll([x], invert(invert(x)) == x), unfold=1)
        self.set_invert = kd.prove(kd.QForAll([x, a], x[a], (~x)[~a]), unfold=1)

        _ones = x.ones & y.ones
        _knowns = Zeros(x) | Zeros(y) | _ones
        self.and_ = kd.notation.and_.define([x, y], KnownBits.mk(_ones, ~_knowns))

        self.and_const = kd.prove(
            kd.QForAll([a, b], const(a) & const(b) == const(a & b)), unfold=1
        )
        # and_top = kd.prove(kd.QForAll([x], x & top == ?), unfold=1)
        self.and_comm = kd.prove(kd.QForAll([x, y], x & y == y & x), unfold=1)
        self.and_assoc = kd.prove(
            kd.QForAll([x, y, z], (x & y) & z == x & (y & z)), unfold=1
        )
        self.set_and = kd.prove(
            kd.QForAll([x, y, a, b], x[a], y[b], (x & y)[a & b]), unfold=1
        )

        _ones = x.ones | y.ones
        _zeros = Zeros(x) & Zeros(y)
        _knowns = _ones | _zeros
        self.or_ = kd.notation.or_.define([x, y], KnownBits.mk(_ones, ~_knowns))

        self.or_const = kd.prove(
            kd.QForAll([a, b], const(a) | const(b) == const(a | b)), unfold=1
        )
        # or_top = kd.prove(kd.QForAll([x], x | top == ?), unfold=1)
        self.or_comm = kd.prove(kd.QForAll([x, y], x | y == y | x), unfold=1)
        self.or_assoc = kd.prove(
            kd.QForAll([x, y, z], (x | y) | z == x | (y | z)), unfold=1
        )
        self.set_or = kd.prove(
            kd.QForAll([x, y, a, b], x[a], y[b], (x | y)[a | b]), unfold=1
        )


@functools.cache
def KB(W):
    return KnownBits(W)


KB1 = KB(1)


def test():
    """
    >>> True
    True
    >>> KB8 = KnownBits(8)
    >>> KB1 = KnownBits(1)
    """
