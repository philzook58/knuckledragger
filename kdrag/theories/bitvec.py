import kdrag as kd
import kdrag.smt as smt

"""
Theorems about bitvectors. These are theorems about the built in smtlib bitvector types
"""


class BVTheory:
    def __init__(self, N):
        self.N = N
        x, y, z = smt.BitVecs("x y z", N)
        zero = smt.BitVecVal(0, N)
        self.zero = zero
        one = smt.BitVecVal(1, N)
        self.one = one

        self.bvadd_comm = kd.lemma(smt.ForAll([x, y], x + y == y + x))
        self.bvadd_assoc = kd.lemma(smt.ForAll([x, y, z], (x + y) + z == x + (y + z)))
        self.bvadd_id = kd.lemma(smt.ForAll([x], x + zero == x))
        self.bvadd_neg = kd.lemma(smt.ForAll([x], x + (-x) == zero))

        self.bvsub_self = kd.lemma(smt.ForAll([x], x - x == zero))
        self.bvsub_def = kd.lemma(smt.ForAll([x, y], x - y == x + (-y)))

        self.bvmul_comm = kd.lemma(smt.ForAll([x, y], x * y == y * x))
        self.bvmul_assoc = kd.lemma(smt.ForAll([x, y, z], (x * y) * z == x * (y * z)))
        self.bvmul_id = kd.lemma(smt.ForAll([x], x * smt.BitVecVal(1, N) == x))
        self.bvmul_zero = kd.lemma(smt.ForAll([x], x * zero == zero))

        self.bvand_comm = kd.lemma(smt.ForAll([x, y], x & y == y & x))
        self.bvand_assoc = kd.lemma(smt.ForAll([x, y, z], (x & y) & z == x & (y & z)))
        self.bvand_id = kd.lemma(smt.ForAll([x], x & smt.BitVecVal(-1, N) == x))
        self.bvand_zero = kd.lemma(smt.ForAll([x], x & zero == zero))

        self.bvor_comm = kd.lemma(smt.ForAll([x, y], x | y == y | x))
        self.bvor_assoc = kd.lemma(smt.ForAll([x, y, z], (x | y) | z == x | (y | z)))
        self.bvor_id = kd.lemma(smt.ForAll([x], x | zero == x))
        self.bvor_neg = kd.lemma(smt.ForAll([x], x | ~x == smt.BitVecVal(-1, N)))

        self.bvxor_comm = kd.lemma(smt.ForAll([x, y], x ^ y == y ^ x))
        self.bvxor_assoc = kd.lemma(smt.ForAll([x, y, z], (x ^ y) ^ z == x ^ (y ^ z)))
        self.bvxor_id = kd.lemma(smt.ForAll([x], x ^ zero == x))
        self.bvxor_self = kd.lemma(smt.ForAll([x], x ^ x == zero))

        self.bvshl_zero = kd.lemma(smt.ForAll([x], x << zero == x))
        self.bvshr_zero = kd.lemma(smt.ForAll([x], smt.LShR(x, zero) == x))

        # Bitwise simplification rules
        self.bvand_self = kd.lemma(smt.ForAll([x], x & x == x))
        self.bvor_self = kd.lemma(smt.ForAll([x], x | x == x))
        self.bvxor_zero = kd.lemma(smt.ForAll([x], x ^ zero == x))
        self.bvnot_self = kd.lemma(smt.ForAll([x], ~x == -x - 1))

        # Rules for shifting and rotating
        self.bvshl_self = kd.lemma(
            smt.ForAll([x, y], x << y == x * (one << y))
        )  # Left shift as multiplication
        # bvshr_self = kd.lemma(smt.ForAll([x, y], smt.LShR(x, y) == x / (one << y)))  # Logical right shift as division
        # bvashr_self = kd.lemma(smt.ForAll([x, y], smt.AShr(x, y) == smt.If(x >> 31 == 0, smt.LShR(x, y), ~smt.LShR(~x, y))))  # Arithmetic right shift rule

        # Simplification with negation and subtraction
        self.bvsub_zero = kd.lemma(smt.ForAll([x], x - zero == x))
        self.bvsub_id = kd.lemma(smt.ForAll([x], zero - x == -x))
        self.bvadd_sub = kd.lemma(smt.ForAll([x, y], x + (-y) == x - y))
        self.bvsub_add = kd.lemma(smt.ForAll([x, y], x - (-y) == x + y))

        # Bitwise AND, OR, and XOR with constants
        self.bvand_allones = kd.lemma(smt.ForAll([x], x & smt.BitVecVal(-1, N) == x))
        self.bvor_allzeros = kd.lemma(smt.ForAll([x], x | zero == x))
        self.bvxor_allzeros = kd.lemma(smt.ForAll([x], x ^ zero == x))

        # Distribution and absorption laws
        self.bvand_or = kd.lemma(
            smt.ForAll([x, y, z], x & (y | z) == (x & y) | (x & z))
        )
        self.bvor_and = kd.lemma(
            smt.ForAll([x, y, z], x | (y & z) == (x | y) & (x | z))
        )
        self.bvand_absorb = kd.lemma(smt.ForAll([x, y], x & (x | y) == x))
        self.bvor_absorb = kd.lemma(smt.ForAll([x, y], x | (x & y) == x))

        # Shifting rules with zero and identity
        self.bvshl_zero_shift = kd.lemma(smt.ForAll([x], x << zero == x))
        self.bvshr_zero_shift = kd.lemma(smt.ForAll([x], smt.LShR(x, zero) == x))
        # bvashr_zero_shift = kd.lemma(smt.ForAll([x], smt.AShr(x, zero) == x))  # Arithmetic right shift by zero is identity
        self.bvshl_allzeros = kd.lemma(smt.ForAll([y], zero << y == zero))
        self.bvshr_allzeros = kd.lemma(smt.ForAll([y], smt.LShR(zero, y) == zero))
        # bvashr_allzeros = kd.lemma(smt.ForAll([y], smt.AShr(zero, y) == zero))  # Arithmetic right shift of zero is zero

        # Additional rules for combining operations
        # bvadd_and = kd.lemma(smt.ForAll([x, y, z], (x & y) + (x & z) == x & (y + z)))  # AND distribution over addition
        self.bvor_and_not = kd.lemma(smt.ForAll([x, y], (x & y) | (x & ~y) == x))
        # bvxor_and_not = kd.lemma(smt.ForAll([x, y], (x & y) ^ (x & ~y) == y))  # Distribution of XOR and AND with negation

        # Properties involving shifts and bit manipulations
        self.bvshl_and = kd.lemma(
            smt.ForAll([x, y, z], (x & y) << z == (x << z) & (y << z))
        )
        self.bvshr_and = kd.lemma(
            smt.ForAll([x, y, z], smt.LShR(x & y, z) == smt.LShR(x, z) & smt.LShR(y, z))
        )
