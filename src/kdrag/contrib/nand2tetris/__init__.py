from kdrag import axiom, prove, Theorem, define, symdef, struct  # noqa: F401
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
from .hack import Nand2State, nand2step

BV16 = BitVecSort(16)

step = nand2step


EMPTYROM = K(BV16, BitVecVal(0, 16))


def init_state(prog: list[int]) -> DatatypeRef:
    rom = EMPTYROM
    for i, v in enumerate(prog):
        rom = Store(rom, i, BitVecVal(v, 16))
    return Nand2State(
        pc=BitVecVal(0, 16),
        rom=rom,
        A=BitVecVal(0, 16),
        D=BitVecVal(0, 16),
        ram=EMPTYROM,
    )


class Dest(Enum):
    NULL = 0b000
    M = 0b001
    D = 0b010
    MD = 0b011
    A = 0b100
    AM = 0b101
    AD = 0b110
    AMD = 0b111


class Comp(Enum):
    ZERO = 0b0101010
    ONE = 0b0111111
    D = 0b0001100
    A = 0b0110000
    M = 0b1110000
    NOT_D = 0b0001101
    NOT_A = 0b0110001
    NOT_M = 0b1110001
    NEG_D = 0b0001111
    NEG_A = 0b0110011
    NEG_M = 0b1110011
    INC_D = 0b0011111
    INC_A = 0b0110111
    INC_M = 0b1110111
    DEC_D = 0b0001110
    DEC_A = 0b0110010
    DEC_M = 0b1110010
    D_PLUS_A = 0b0000010
    D_PLUS_M = 0b1000010
    D_MINUS_A = 0b0010011
    D_MINUS_M = 0b1010011
    A_MINUS_D = 0b0000111
    M_MINUS_D = 0b1000111
    D_AND_A = 0b0000000
    D_AND_M = 0b1000000
    D_OR_A = 0b0010101
    D_OR_M = 0b1010101


class Jmp(Enum):
    NULL = 0b000
    JGT = 0b001
    JEQ = 0b010
    JGE = 0b011
    JLT = 0b100
    JNE = 0b101
    JLE = 0b110
    JMP = 0b111


def ainsn(a: int) -> int:
    return a & 0b111111111111111


def cinsn(dst: Dest, comp: Comp, jmp=Jmp.NULL) -> int:
    return (0b111 << 13) | (dst.value << 3) | (comp.value << 6) | jmp.value


def ppinsn(insn: int) -> str:
    if (insn >> 15) == 0:
        return f"@{insn & 0b111111111111111}"
    else:
        dst = Dest((insn >> 3) & 0b111)
        comp = Comp((insn >> 6) & 0b1111111)
        jmp = Jmp(insn & 0b111)
        return f"{dst.name}={comp.name};{jmp.name}"
