"""
Theorems about bitvectors. These are theorems about the built in smtlib bitvector types
"""

import kdrag as kd
from kdrag import NewType, define, prove
import kdrag.smt as smt
from kdrag.smt import (
    Array,
    BV2Int,
    BitVec,
    BitVecVal,
    BitVecs,
    Concat,
    Const,
    Consts,
    Empty,
    Extract,
    ForAll,
    Function,
    If,
    IntSort,
    IntVal,
    LShR,
    Lambda,
    Length,
    SeqMap,
    Store,
    SubSeq,
    Unit,
    simplify,
)
import kdrag.theories.seq as seq
import functools


@functools.cache
def BitVecSort(N):
    """

    >>> BV32 = BitVecSort(32)
    >>> BV32.bvadd_comm
    |= ForAll([x, y], x + y == y + x)
    """
    S = smt.BitVecSort(N)
    smt.sort_registry[S.get_id()] = S
    x, y, z = BitVecs("x y z", N)
    zero = BitVecVal(0, N)
    S.BVNot = (~x).decl()
    S.zero = zero
    one = BitVecVal(1, N)
    S.one = one

    S.bvadd_comm = prove(ForAll([x, y], x + y == y + x))
    S.bvadd_assoc = prove(ForAll([x, y, z], (x + y) + z == x + (y + z)))
    S.bvadd_id = prove(ForAll([x], x + zero == x))
    S.bvadd_neg = prove(ForAll([x], x + (-x) == zero))

    S.bvsub_self = prove(ForAll([x], x - x == zero))
    S.bvsub_def = prove(ForAll([x, y], x - y == x + (-y)))

    S.bvmul_comm = prove(ForAll([x, y], x * y == y * x))
    S.bvmul_assoc = prove(ForAll([x, y, z], (x * y) * z == x * (y * z)))
    S.bvmul_id = prove(ForAll([x], x * BitVecVal(1, N) == x))
    S.bvmul_zero = prove(ForAll([x], x * zero == zero))

    S.bvand_comm = prove(ForAll([x, y], x & y == y & x))
    S.bvand_assoc = prove(ForAll([x, y, z], (x & y) & z == x & (y & z)))
    S.bvand_id = prove(ForAll([x], x & BitVecVal(-1, N) == x))
    S.bvand_zero = prove(ForAll([x], x & zero == zero))

    S.bvor_comm = prove(ForAll([x, y], x | y == y | x))
    S.bvor_assoc = prove(ForAll([x, y, z], (x | y) | z == x | (y | z)))
    S.bvor_id = prove(ForAll([x], x | zero == x))
    S.bvor_neg = prove(ForAll([x], x | ~x == BitVecVal(-1, N)))

    S.bvxor_comm = prove(ForAll([x, y], x ^ y == y ^ x))
    S.bvxor_assoc = prove(ForAll([x, y, z], (x ^ y) ^ z == x ^ (y ^ z)))
    S.bvxor_id = prove(ForAll([x], x ^ zero == x))
    S.bvxor_self = prove(ForAll([x], x ^ x == zero))

    S.bvshl_zero = prove(ForAll([x], x << zero == x))
    S.bvshr_zero = prove(ForAll([x], LShR(x, zero) == x))

    # Bitwise simplification rules
    S.bvand_self = prove(ForAll([x], x & x == x))
    S.bvor_self = prove(ForAll([x], x | x == x))
    S.bvxor_zero = prove(ForAll([x], x ^ zero == x))
    S.bvnot_self = prove(ForAll([x], ~x == -x - 1))

    # Rules for shifting and rotating
    S.bvshl_self = prove(
        ForAll([x, y], x << y == x * (one << y))
    )  # Left shift as multiplication
    # bvshr_self = kd.prove(smt.ForAll([x, y], smt.LShR(x, y) == x / (one << y)))  # Logical right shift as division
    # bvashr_self = kd.prove(smt.ForAll([x, y], smt.AShr(x, y) == smt.If(x >> 31 == 0, smt.LShR(x, y), ~smt.LShR(~x, y))))  # Arithmetic right shift rule

    # Simplification with negation and subtraction
    S.bvsub_zero = prove(ForAll([x], x - zero == x))
    S.bvsub_id = prove(ForAll([x], zero - x == -x))
    S.bvadd_sub = prove(ForAll([x, y], x + (-y) == x - y))
    S.bvsub_add = prove(ForAll([x, y], x - (-y) == x + y))

    # Bitwise AND, OR, and XOR with constants
    S.bvand_allones = prove(ForAll([x], x & BitVecVal(-1, N) == x))
    S.bvor_allzeros = prove(ForAll([x], x | zero == x))
    S.bvxor_allzeros = prove(ForAll([x], x ^ zero == x))

    # Distribution and absorption laws
    S.bvand_or = prove(ForAll([x, y, z], x & (y | z) == (x & y) | (x & z)))
    S.bvor_and = prove(ForAll([x, y, z], x | (y & z) == (x | y) & (x | z)))
    S.bvand_absorb = prove(ForAll([x, y], x & (x | y) == x))
    S.bvor_absorb = prove(ForAll([x, y], x | (x & y) == x))

    # Shifting rules with zero and identity
    S.bvshl_zero_shift = prove(ForAll([x], x << zero == x))
    S.bvshr_zero_shift = prove(ForAll([x], LShR(x, zero) == x))
    # bvashr_zero_shift = kd.prove(smt.ForAll([x], smt.AShr(x, zero) == x))  # Arithmetic right shift by zero is identity
    S.bvshl_allzeros = prove(ForAll([y], zero << y == zero))
    S.bvshr_allzeros = prove(ForAll([y], LShR(zero, y) == zero))
    # bvashr_allzeros = kd.prove(smt.ForAll([y], smt.AShr(zero, y) == zero))  # Arithmetic right shift of zero is zero

    # Additional rules for combining operations
    # bvadd_and = kd.prove(smt.ForAll([x, y, z], (x & y) + (x & z) == x & (y + z)))  # AND distribution over addition
    S.bvor_and_not = prove(ForAll([x, y], (x & y) | (x & ~y) == x))
    # bvxor_and_not = kd.prove(smt.ForAll([x, y], (x & y) ^ (x & ~y) == y))  # Distribution of XOR and AND with negation

    # Properties involving shifts and bit manipulations
    S.bvshl_and = prove(ForAll([x, y, z], (x & y) << z == (x << z) & (y << z)))
    S.bvshr_and = prove(ForAll([x, y, z], LShR(x & y, z) == LShR(x, z) & LShR(y, z)))
    return S


BV1 = BitVecSort(1)
BV8 = BitVecSort(8)
# Annoyingly slow ~ 1s
# BV16 = BitVecSort(16)
# BV32 = BitVecSort(32)
# Annoyingly slow ~ 1s
# BV64 = BitVecSort(64)


BitVecN = NewType("BitVecN", seq.Seq(BV1))
"""
Arbitrary length bitvectors. Least significant bit comes first (index 0). Concat is unfortunately reversed compared to bitvector convetions.

Fix via Newtype wrapper? I guess I want overloading anyway

"""

BVN = BitVecN
BVN.empty = BVN(Empty(seq.Seq(BV1)))
x, y, z = Consts("x y z", BitVecN)
to_int = Function("BitVecN.to_int", BitVecN, IntSort())
to_int = kd.notation.to_int.define(
    [x],
    If(
        Length(x.val) == 0,
        IntVal(0),
        BV2Int(x.val[0], is_signed=False)
        + 2 * to_int(BitVecN(SubSeq(x.val, 1, Length(x.val) - 1))),
    ),
)


def BitVecNVal(x: int, N: int) -> smt.DatatypeRef:
    """
    >>> BitVecNVal(6, 3)
    BitVecN(Concat(Unit(0), Concat(Unit(1), Unit(1))))
    """
    if N == 0:
        return BVN.empty
    elif N == 1:
        return BVN(Unit(BitVecVal(x, 1)))
    else:
        return BVN(Concat([Unit(BitVecVal((x >> i) & 1, 1)) for i in range(N)]))


to_int_empty = prove(to_int(BitVecNVal(0, 0)) == IntVal(0), unfold=1)
to_int_false = prove(BitVecNVal(0, 1).to_int() == IntVal(0), by=[to_int.defn])
to_int_true = prove(BitVecNVal(1, 1).to_int() == IntVal(1), by=[to_int.defn])
# (x + y).to_int() == x.to_int() + 2**(smt.Length(x)) * y.to_int()


def fromBV(x: smt.BitVecRef) -> smt.DatatypeRef:
    """
    >>> fromBV(BitVecVal(6, 3))
    BitVecN(Concat(Unit(0), Concat(Unit(1), Unit(1))))
    """
    return simplify(BitVecN(Concat([Unit(Extract(i, i, x)) for i in range(x.size())])))


def toBV(x: smt.DatatypeRef, N: int) -> smt.BitVecRef:
    """
    >>> simplify(toBV(BitVecNVal(6, 3), 3))
    6
    """
    BV = BitVecSort(N)
    undef = Function("toBV_undef", BitVecN, BV)
    unpack = Concat(*reversed([x.val[i] for i in range(N)]))
    # could possibly raise error here if we _know_ you've reduced to undef
    # assert not smt.simplify(expr).eq(smt.simplify(undef(x)))
    return If(
        Length(x.val) == N,
        unpack,  # smt.Int2BV(to_int(x), N),  # Or could do full unpack
        undef(x),
    )


def BitVecNConst(name: str, N: int) -> smt.DatatypeRef:
    """
    There is a lot of confusion possible with this construct. Maybe it shouldn't exist.

    >>> BitVecNConst("x", 3)
    BitVecN(Concat(Unit(x[0]), Concat(Unit(x[1]), Unit(x[2]))))
    """
    x = Array(name, IntSort(), BV1)  # array vs function vs seq?
    return BitVecN(Concat([Unit(x[i]) for i in range(N)]))


def BVNot(x: smt.DatatypeRef) -> smt.DatatypeRef:
    """
    >>> simplify(BVNot(BitVecNVal(1, 3)))
    BitVecN(Concat(Unit(0), Concat(Unit(1), Unit(1))))
    """
    z = Const("z", smt.BitVecSort(1))
    return BitVecN(SeqMap(Lambda([z], BV1.BVNot(z)), x.val))


# BVAdd SeqFold


def SelectConcat(
    a: smt.ArrayRef, addr: smt.BitVecRef | int, n: int, le=True
) -> smt.BitVecRef:
    """
    Concat out of an array.
    n is number of bytes.
    Flag is for little endian concatenation vs big endian.

    >>> x = Const("x", BitVecSort(8))
    >>> a = Lambda([x], x)
    >>> simplify(SelectConcat(a, 1, 1))
    1
    >>> simplify(SelectConcat(a, 0, 2))
    256
    >>> simplify(SelectConcat(a, 0, 2, le=False))
    1
    """
    assert n > 0
    if n == 1:
        return a[addr]
    elif le:
        return Concat([a[addr + n - i - 1] for i in range(n)])
    else:
        return Concat([a[addr + i] for i in range(n)])


@functools.cache
def select_concats(bits, size, le=True):
    _a = Array("a", smt.BitVecSort(bits), smt.BitVecSort(8))
    _addr = BitVec("addr", bits)
    return define(
        f"select{size}{'le' if le else 'be'}",
        [_a, _addr],
        SelectConcat(_a, _addr, size // 8, le=le),
    )


def select_concat(
    a: smt.ArrayRef, addr: smt.BitVecRef | int, n: int, le=True
) -> smt.BitVecRef:
    """
    >>> mem = Array("mem", smt.BitVecSort(64), BV8)
    >>> select_concat(mem, 0, 2)
    select16le(mem, 0)
    """
    if n == 1:
        return a[addr]
    else:
        return select_concats(a.domain().size(), n * 8, le=le)(a, addr)
        # return select_concats[a.domain().size()][le][n * 8](a, addr)


def StoreConcat(
    a: smt.ArrayRef, addr: smt.BitVecRef | int, data: smt.BitVecRef, le=True
) -> smt.ArrayRef:
    """
    Store multiple bytes into an array.

    >>> a = Array("a", smt.BitVecSort(8), smt.BitVecSort(8))
    >>> simplify(StoreConcat(a, 0, BitVecVal(258, 16)))
    Store(Store(a, 0, 2), 1, 1)
    >>> simplify(SelectConcat(StoreConcat(a, 6, BitVecVal(258, 16)), 6, 2))
    258
    >>> simplify(SelectConcat(StoreConcat(a, 6, BitVecVal(258, 16), le=False), 6, 2, le=False))
    258
    """
    n = data.size()
    assert n % 8 == 0
    for offset in range(n // 8):
        if le:
            a = Store(a, addr + offset, Extract(8 * offset + 7, 8 * offset, data))
        else:
            a = Store(
                a,
                addr + n // 8 - offset - 1,
                Extract(8 * offset + 7, 8 * offset, data),
            )
    return a


@functools.cache
def store_concats(bits, size, le=True):
    _a = Array("a", smt.BitVecSort(bits), smt.BitVecSort(8))
    _addr = BitVec("addr", bits)
    data = BitVec("data", size)
    return define(
        f"store{size}{'le' if le else 'be'}",
        [_a, _addr, data],
        StoreConcat(_a, _addr, data, le=le),
    )


def store_concat(
    a: smt.ArrayRef, addr: smt.BitVecRef | int, data: smt.BitVecRef, le=True
) -> smt.ArrayRef:
    n = data.size()
    if n == 8:
        return Store(a, addr, data)
    else:
        return store_concats(a.domain().size(), n, le=le)(a, addr, data)


def PopCount(x: smt.BitVecRef) -> smt.ArithRef:
    """
    >>> simplify(PopCount(BitVecVal(6, 3)))
    2
    """
    size = x.size()
    out = BitVecVal(0, size)
    for i in range(size):
        out += (x >> i) & 1
    return out
    # return smt.Sum([smt.BV2Int(smt.Extract(i, i, x)) for i in range(x.size())])


@functools.cache
def popcounts(size: int) -> smt.FuncDeclRef:
    x = BitVec("x", size)
    return define("popcount" + str(size), [x], PopCount(x))


def popcount(x: smt.BitVecRef):
    return popcounts(x.size())(x)


def UnConcat(x: smt.BitVecRef, lane_num: int) -> list[smt.BitVecRef]:
    """
    Unpack a bitvector into lanes.

    >>> x,y = BitVecs("x y", 32)
    >>> prove(Concat(UnConcat(x, 4)) == x)
    |= Concat(Concat(Concat(Extract(31, 24, x), Extract(23, 16, x)),
                  Extract(15, 8, x)),
           Extract(7, 0, x)) == x
    >>> prove(UnConcat(Concat(x,y), 2)[0] == x)
    |= Extract(63, 32, Concat(x, y)) == x
    """
    assert x.size() % lane_num == 0
    lanesize = x.size() // lane_num
    return [
        Extract((i + 1) * lanesize - 1, i * lanesize, x)
        for i in reversed(range(lane_num))
    ]


def vmap(f, n):
    """

    >>> x,y = BitVecs("x y", 16)
    >>> prove(vmap(lambda a: a, 2)(x) == x)
    |= Concat(Extract(15, 8, x), Extract(7, 0, x)) == x
    >>> vmap(lambda a,b: a - b, 2)(x, y)
    Concat(Extract(15, 8, x) - Extract(15, 8, y),
           Extract(7, 0, x) - Extract(7, 0, y))
    """

    def res(*args):
        return Concat(
            [f(*smallargs) for smallargs in zip(*[UnConcat(arg, n) for arg in args])]
        )

    return res
