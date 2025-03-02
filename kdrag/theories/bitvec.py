import kdrag as kd
import kdrag.smt as smt
import kdrag.theories.seq as seq
import functools

"""
Theorems about bitvectors. These are theorems about the built in smtlib bitvector types
"""


@functools.cache
def BitVecSort(N):
    """

    >>> BV32 = BitVecSort(32)
    >>> BV32.bvadd_comm
    |- ForAll([x, y], x + y == y + x)
    """
    S = smt.BitVecSort(N)
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
BitVecN = kd.NewType("BitVecN", seq.Seq(BV1))
"""
Arbitrary length bitvectors. Least significant bit comes first (index 0). Concat is unfortunately reversed compared to bitvector convetions.

Fix via Newtype wrapper? I guess I want overloading anyway

"""

BVN = BitVecN
BVN.empty = BVN(smt.Empty(seq.Seq(BV1)))
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


def BitVecNVal(x: int, N: int) -> smt.SeqRef:
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


def BVNot(x: smt.DatatypeRef) -> smt.SeqRef:
    """
    >>> smt.simplify(BVNot(BitVecNVal(1, 3)))
    BitVecN(Concat(Unit(0), Concat(Unit(1), Unit(1))))
    """
    z = smt.Const("z", smt.BitVecSort(1))
    return BitVecN(smt.SeqMap(smt.Lambda([z], BV1.BVNot(z)), x.val))


# BVAdd SeqFold
