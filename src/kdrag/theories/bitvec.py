"""
Theorems about bitvectors. These are theorems about the built in smtlib bitvector types
"""

import kdrag as kd
import kdrag.smt as smt
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
    x, y, z = smt.BitVecs("x y z", N)
    zero = smt.BitVecVal(0, N)
    S.BVNot = (~x).decl()
    S.zero = zero
    one = smt.BitVecVal(1, N)
    S.one = one

    S.bvadd_comm = kd.prove(smt.ForAll([x, y], x + y == y + x))
    S.bvadd_assoc = kd.prove(smt.ForAll([x, y, z], (x + y) + z == x + (y + z)))
    S.bvadd_id = kd.prove(smt.ForAll([x], x + zero == x))
    S.bvadd_neg = kd.prove(smt.ForAll([x], x + (-x) == zero))

    S.bvsub_self = kd.prove(smt.ForAll([x], x - x == zero))
    S.bvsub_def = kd.prove(smt.ForAll([x, y], x - y == x + (-y)))

    S.bvmul_comm = kd.prove(smt.ForAll([x, y], x * y == y * x))
    S.bvmul_assoc = kd.prove(smt.ForAll([x, y, z], (x * y) * z == x * (y * z)))
    S.bvmul_id = kd.prove(smt.ForAll([x], x * smt.BitVecVal(1, N) == x))
    S.bvmul_zero = kd.prove(smt.ForAll([x], x * zero == zero))

    S.bvand_comm = kd.prove(smt.ForAll([x, y], x & y == y & x))
    S.bvand_assoc = kd.prove(smt.ForAll([x, y, z], (x & y) & z == x & (y & z)))
    S.bvand_id = kd.prove(smt.ForAll([x], x & smt.BitVecVal(-1, N) == x))
    S.bvand_zero = kd.prove(smt.ForAll([x], x & zero == zero))

    S.bvor_comm = kd.prove(smt.ForAll([x, y], x | y == y | x))
    S.bvor_assoc = kd.prove(smt.ForAll([x, y, z], (x | y) | z == x | (y | z)))
    S.bvor_id = kd.prove(smt.ForAll([x], x | zero == x))
    S.bvor_neg = kd.prove(smt.ForAll([x], x | ~x == smt.BitVecVal(-1, N)))

    S.bvxor_comm = kd.prove(smt.ForAll([x, y], x ^ y == y ^ x))
    S.bvxor_assoc = kd.prove(smt.ForAll([x, y, z], (x ^ y) ^ z == x ^ (y ^ z)))
    S.bvxor_id = kd.prove(smt.ForAll([x], x ^ zero == x))
    S.bvxor_self = kd.prove(smt.ForAll([x], x ^ x == zero))

    S.bvshl_zero = kd.prove(smt.ForAll([x], x << zero == x))
    S.bvshr_zero = kd.prove(smt.ForAll([x], smt.LShR(x, zero) == x))

    # Bitwise simplification rules
    S.bvand_self = kd.prove(smt.ForAll([x], x & x == x))
    S.bvor_self = kd.prove(smt.ForAll([x], x | x == x))
    S.bvxor_zero = kd.prove(smt.ForAll([x], x ^ zero == x))
    S.bvnot_self = kd.prove(smt.ForAll([x], ~x == -x - 1))

    # Rules for shifting and rotating
    S.bvshl_self = kd.prove(
        smt.ForAll([x, y], x << y == x * (one << y))
    )  # Left shift as multiplication
    # bvshr_self = kd.prove(smt.ForAll([x, y], smt.LShR(x, y) == x / (one << y)))  # Logical right shift as division
    # bvashr_self = kd.prove(smt.ForAll([x, y], smt.AShr(x, y) == smt.If(x >> 31 == 0, smt.LShR(x, y), ~smt.LShR(~x, y))))  # Arithmetic right shift rule

    # Simplification with negation and subtraction
    S.bvsub_zero = kd.prove(smt.ForAll([x], x - zero == x))
    S.bvsub_id = kd.prove(smt.ForAll([x], zero - x == -x))
    S.bvadd_sub = kd.prove(smt.ForAll([x, y], x + (-y) == x - y))
    S.bvsub_add = kd.prove(smt.ForAll([x, y], x - (-y) == x + y))

    # Bitwise AND, OR, and XOR with constants
    S.bvand_allones = kd.prove(smt.ForAll([x], x & smt.BitVecVal(-1, N) == x))
    S.bvor_allzeros = kd.prove(smt.ForAll([x], x | zero == x))
    S.bvxor_allzeros = kd.prove(smt.ForAll([x], x ^ zero == x))

    # Distribution and absorption laws
    S.bvand_or = kd.prove(smt.ForAll([x, y, z], x & (y | z) == (x & y) | (x & z)))
    S.bvor_and = kd.prove(smt.ForAll([x, y, z], x | (y & z) == (x | y) & (x | z)))
    S.bvand_absorb = kd.prove(smt.ForAll([x, y], x & (x | y) == x))
    S.bvor_absorb = kd.prove(smt.ForAll([x, y], x | (x & y) == x))

    # Shifting rules with zero and identity
    S.bvshl_zero_shift = kd.prove(smt.ForAll([x], x << zero == x))
    S.bvshr_zero_shift = kd.prove(smt.ForAll([x], smt.LShR(x, zero) == x))
    # bvashr_zero_shift = kd.prove(smt.ForAll([x], smt.AShr(x, zero) == x))  # Arithmetic right shift by zero is identity
    S.bvshl_allzeros = kd.prove(smt.ForAll([y], zero << y == zero))
    S.bvshr_allzeros = kd.prove(smt.ForAll([y], smt.LShR(zero, y) == zero))
    # bvashr_allzeros = kd.prove(smt.ForAll([y], smt.AShr(zero, y) == zero))  # Arithmetic right shift of zero is zero

    # Additional rules for combining operations
    # bvadd_and = kd.prove(smt.ForAll([x, y, z], (x & y) + (x & z) == x & (y + z)))  # AND distribution over addition
    S.bvor_and_not = kd.prove(smt.ForAll([x, y], (x & y) | (x & ~y) == x))
    # bvxor_and_not = kd.prove(smt.ForAll([x, y], (x & y) ^ (x & ~y) == y))  # Distribution of XOR and AND with negation

    # Properties involving shifts and bit manipulations
    S.bvshl_and = kd.prove(smt.ForAll([x, y, z], (x & y) << z == (x << z) & (y << z)))
    S.bvshr_and = kd.prove(
        smt.ForAll([x, y, z], smt.LShR(x & y, z) == smt.LShR(x, z) & smt.LShR(y, z))
    )
    return S


BV1 = BitVecSort(1)
BV8 = BitVecSort(8)
# Annoyingly slow ~ 1s
# BV16 = BitVecSort(16)
# BV32 = BitVecSort(32)
# Annoyingly slow ~ 1s
# BV64 = BitVecSort(64)


BitVecN = kd.NewType("BitVecN", seq.Seq(BV1))
"""
Arbitrary length bitvectors. Least significant bit comes first (index 0). Concat is unfortunately reversed compared to bitvector convetions.

Fix via Newtype wrapper? I guess I want overloading anyway

"""

BVN = BitVecN
BVN.empty = BVN(smt.Empty(seq.Seq(BV1)))  # type: ignore
x, y, z = smt.Consts("x y z", BitVecN)
to_int = smt.Function("to_int", BitVecN, smt.IntSort())
to_int = kd.notation.to_int.define(
    [x],
    smt.If(
        smt.Length(x.val) == 0,
        smt.IntVal(0),
        smt.BV2Int(x.val[0], is_signed=False)
        + 2 * to_int(BitVecN(smt.SubSeq(x.val, 1, smt.Length(x.val) - 1))),
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
        return BVN(smt.Unit(smt.BitVecVal(x, 1)))
    else:
        return BVN(
            smt.Concat([smt.Unit(smt.BitVecVal((x >> i) & 1, 1)) for i in range(N)])
        )


to_int_empty = kd.prove(to_int(BitVecNVal(0, 0)) == smt.IntVal(0), unfold=1)
to_int_false = kd.prove(BitVecNVal(0, 1).to_int() == smt.IntVal(0), by=[to_int.defn])
to_int_true = kd.prove(BitVecNVal(1, 1).to_int() == smt.IntVal(1), by=[to_int.defn])
# (x + y).to_int() == x.to_int() + 2**(smt.Length(x)) * y.to_int()


def fromBV(x: smt.BitVecRef) -> smt.DatatypeRef:
    """
    >>> fromBV(smt.BitVecVal(6, 3))
    BitVecN(Concat(Unit(0), Concat(Unit(1), Unit(1))))
    """
    return smt.simplify(
        BitVecN(smt.Concat([smt.Unit(smt.Extract(i, i, x)) for i in range(x.size())]))
    )


def toBV(x: smt.DatatypeRef, N: int) -> smt.BitVecRef:
    """
    >>> smt.simplify(toBV(BitVecNVal(6, 3), 3))
    6
    """
    BV = BitVecSort(N)
    undef = smt.Function("toBV_undef", BitVecN, BV)
    unpack = smt.Concat(*reversed([x.val[i] for i in range(N)]))
    # could possibly raise error here if we _know_ you've reduced to undef
    # assert not smt.simplify(expr).eq(smt.simplify(undef(x)))
    return smt.If(
        smt.Length(x.val) == N,
        unpack,  # smt.Int2BV(to_int(x), N),  # Or could do full unpack
        undef(x),
    )


def BitVecNConst(name: str, N: int) -> smt.DatatypeRef:
    """
    There is a lot of confusion possible with this construct. Maybe it shouldn't exist.

    >>> BitVecNConst("x", 3)
    BitVecN(Concat(Unit(x[0]), Concat(Unit(x[1]), Unit(x[2]))))
    """
    x = smt.Array(name, smt.IntSort(), BV1)  # array vs function vs seq?
    return BitVecN(smt.Concat([smt.Unit(x[i]) for i in range(N)]))


def BVNot(x: smt.DatatypeRef) -> smt.DatatypeRef:
    """
    >>> smt.simplify(BVNot(BitVecNVal(1, 3)))
    BitVecN(Concat(Unit(0), Concat(Unit(1), Unit(1))))
    """
    z = smt.Const("z", smt.BitVecSort(1))
    return BitVecN(smt.SeqMap(smt.Lambda([z], BV1.BVNot(z)), x.val))


# BVAdd SeqFold


def SelectConcat(
    a: smt.ArrayRef, addr: smt.BitVecRef | int, n: int, le=True
) -> smt.BitVecRef:
    """
    Concat out of an array.
    n is number of bytes.
    Flag is for little endian concatenation vs big endian.

    >>> x = smt.Const("x", BitVecSort(8))
    >>> a = smt.Lambda([x], x)
    >>> smt.simplify(SelectConcat(a, 1, 1))
    1
    >>> smt.simplify(SelectConcat(a, 0, 2))
    256
    >>> smt.simplify(SelectConcat(a, 0, 2, le=False))
    1
    """
    assert n > 0
    if n == 1:
        return a[addr]
    elif le:
        return smt.Concat([a[addr + n - i - 1] for i in range(n)])
    else:
        return smt.Concat([a[addr + i] for i in range(n)])


def StoreConcat(
    a: smt.ArrayRef, addr: smt.BitVecRef | int, data: smt.BitVecRef, le=True
) -> smt.ArrayRef:
    """
    Store multiple bytes into an array.

    >>> a = smt.Array("a", smt.BitVecSort(8), smt.BitVecSort(8))
    >>> smt.simplify(StoreConcat(a, 0, smt.BitVecVal(258, 16)))
    Store(Store(a, 0, 2), 1, 1)
    >>> smt.simplify(SelectConcat(StoreConcat(a, 6, smt.BitVecVal(258, 16)), 6, 2))
    258
    """
    n = data.size()
    assert n % 8 == 0
    for offset in range(n // 8):
        if le:
            a = smt.Store(
                a, addr + offset, smt.Extract(8 * offset + 7, 8 * offset, data)
            )
        else:
            a = smt.Store(
                a, addr + offset, smt.Extract(8 * offset, 8 * offset + 7, data)
            )
    return a


# @functools.cache
# def select64(outsize: int) -> smt.FuncDeclRef:
#     addr = smt.BitVec("addr", 64)
#     a = smt.Array("a", smt.BitVecSort(64), smt.BitVecSort(8))
#     return kd.define("select64", [a, addr], SelectConcat(a, addr, outsize))
_addr = smt.BitVec("addr", 64)
_a = smt.Array("a", smt.BitVecSort(64), smt.BitVecSort(8))
bitsizes = [16, 32, 64]
select64_le = {
    size: kd.define(
        f"select_{size}_le", [_a, _addr], SelectConcat(_a, _addr, size // 8, le=True)
    )
    for size in bitsizes
}
select64_be = {
    size: kd.define(
        f"select_{size}_be", [_a, _addr], SelectConcat(_a, _addr, size // 8, le=False)
    )
    for size in bitsizes
}
_addr = smt.BitVec("addr", 32)
_a = smt.Array("a", smt.BitVecSort(32), smt.BitVecSort(8))
select32_le = {
    size: kd.define(
        f"select_{size}_le", [_a, _addr], SelectConcat(_a, _addr, size // 8, le=True)
    )
    for size in bitsizes
}
select32_be = {
    size: kd.define(
        f"select_{size}_be", [_a, _addr], SelectConcat(_a, _addr, size // 8, le=False)
    )
    for size in bitsizes
}
select_concats = {
    32: {True: select32_le, False: select32_be},
    64: {True: select64_le, False: select64_be},
}


def select_concat(
    a: smt.ArrayRef, addr: smt.BitVecRef | int, n: int, le=True
) -> smt.BitVecRef:
    """
    >>> mem = smt.Array("mem", smt.BitVecSort(64), BV8)
    >>> smt.simplify(select_concat(mem, 0, 2))
    select_16_le(mem, 0)
    """
    return select_concats[a.domain().size()][le][n * 8](a, addr)


def PopCount(x: smt.BitVecRef) -> smt.ArithRef:
    """
    >>> smt.simplify(PopCount(smt.BitVecVal(6, 3)))
    2
    """
    return smt.Sum([smt.BV2Int(smt.Extract(i, i, x)) for i in range(x.size())])


def UnConcat(x: smt.BitVecRef, lane_num: int) -> list[smt.BitVecRef]:
    """
    Unpack a bitvector into lanes.

    >>> x,y = smt.BitVecs("x y", 32)
    >>> kd.prove(smt.Concat(UnConcat(x, 4)) == x)
    |= Concat(Concat(Concat(Extract(31, 24, x), Extract(23, 16, x)),
                  Extract(15, 8, x)),
           Extract(7, 0, x)) == x
    >>> kd.prove(UnConcat(smt.Concat(x,y), 2)[0] == x)
    |= Extract(63, 32, Concat(x, y)) == x
    """
    assert x.size() % lane_num == 0
    lanesize = x.size() // lane_num
    return [
        smt.Extract((i + 1) * lanesize - 1, i * lanesize, x)
        for i in reversed(range(lane_num))
    ]


def vmap(f, n):
    """

    >>> x,y = smt.BitVecs("x y", 16)
    >>> kd.prove(vmap(lambda a: a, 2)(x) == x)
    |= Concat(Extract(15, 8, x), Extract(7, 0, x)) == x
    >>> vmap(lambda a,b: a - b, 2)(x, y)
    Concat(Extract(15, 8, x) - Extract(15, 8, y),
           Extract(7, 0, x) - Extract(7, 0, y))
    """

    def res(*args):
        return smt.Concat(
            [f(*smallargs) for smallargs in zip(*[UnConcat(arg, n) for arg in args])]
        )

    return res
