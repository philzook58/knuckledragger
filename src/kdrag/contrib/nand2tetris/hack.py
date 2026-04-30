# type: ignore
from kdrag import axiom, prove, Theorem, define, symdef, struct, Struct  # noqa: F401
from kdrag.smt import (
    ForAll,
    Exists,
    Implies,
    And,
    Or,
    Not,
    If,
    IntVal,
    BitVecSort,
    ArraySort,
    Store,
    BitVecVal,
    K,
    BoolVal,
    DatatypeRef,
    BitVec,
)  # noqa: F401
from enum import Enum

BV16 = BitVecSort(16)


"""
@struct
class Nand2State:
    pc: BV16
    rom: ArraySort(BV16, BV16)  # Or in decoded form?
    ram: ArraySort(BV16, BV16)
    D: BV16
    A: BV16
"""


Nand2State = Struct(
    "Nand2State",
    ("pc", BV16),
    ("rom", ArraySort(BV16, BV16)),  # Or in decoded form?
    ("ram", ArraySort(BV16, BV16)),
    ("D", BV16),
    ("A", BV16),
)


@symdef
def nand2step(st: Nand2State) -> Nand2State:
    insn = st.rom[st.pc]
    M = st.rom[st.A]
    is_A = (insn >> 15) == 0
    if is_A:
        st.pc = st.pc + 1
        st.A = insn
        return st
    else:
        comp = (insn >> 6) & 0b1111111
        dest = (insn >> 3) & 0b111
        jump = insn & 0b111
        if comp == 0b0101010:
            out = BitVecVal(0, 16)
        elif comp == 0b0111111:
            out = BitVecVal(1, 16)
        elif comp == 0b0111010:
            out = BitVecVal(-1, 16)
        elif comp == 0b0001100:
            out = st.D
        elif comp == 0b0110000:
            out = st.A
        elif comp == 0b1110000:
            out = M
        elif comp == 0b0001101:
            out = ~st.D
        elif comp == 0b0110001:
            out = ~st.A
        elif comp == 0b1110001:
            out = ~M
        elif comp == 0b0001111:
            out = -st.D
        elif comp == 0b0110011:
            out = -st.A
        elif comp == 0b1110011:
            out = -M
        elif comp == 0b0011111:
            out = st.D + 1
        elif comp == 0b0110111:
            out = st.A + 1
        elif comp == 0b1110111:
            out = M + 1
        elif comp == 0b0001110:
            out = st.D - 1
        elif comp == 0b0110010:
            out = st.A - 1
        elif comp == 0b1110010:
            out = M - 1
        elif comp == 0b0000010:
            out = st.D + st.A
        elif comp == 0b1000010:
            out = st.D + M
        elif comp == 0b0010011:
            out = st.D - st.A
        elif comp == 0b1010011:
            out = st.D - M
        elif comp == 0b0000111:
            out = st.A - st.D
        elif comp == 0b1000111:
            out = M - st.D
        elif comp == 0b0000000:
            out = st.D & st.A
        elif comp == 0b1000000:
            out = st.D & M
        elif comp == 0b0010101:
            out = st.D | st.A
        elif comp == 0b1010101:
            out = st.D | M
        else:
            out = BitVec("undefined_comp", 16)

        if dest == 0b000:
            pass
        elif dest == 0b001:
            st.ram = Store(st.ram, st.A, out)
        elif dest == 0b010:
            st.D = out
        elif dest == 0b011:
            st.ram = Store(st.ram, st.A, out)
            st.D = out
        elif dest == 0b100:
            st.A = out
        elif dest == 0b101:
            st.ram = Store(st.ram, st.A, out)
            st.A = out
        elif dest == 0b110:
            st.D = out
            st.A = out
        elif dest == 0b111:
            st.ram = Store(st.ram, st.A, out)
            st.D = out
            st.A = out
        else:
            assert False, "Impossible"

        if jump == 0b000:
            cond = BoolVal(False)
        elif jump == 0b001:
            cond = out > 0
        elif jump == 0b010:
            cond = out == 0
        elif jump == 0b011:
            cond = out >= 0
        elif jump == 0b100:
            cond = out < 0
        elif jump == 0b101:
            cond = out != 0
        elif jump == 0b110:
            cond = out <= 0
        elif jump == 0b111:
            cond = BoolVal(True)
        else:
            cond = BoolVal(False)  # Impossible
            assert False, "Impossible"
        st.pc = If(cond, st.A, st.pc + 1)
        return st
