# Ghidra emulator

# https://github.com/NationalSecurityAgency/ghidra/blob/master/Ghidra/Features/Decompiler/src/decompile/cpp/emulate.cc
# https://github.com/NationalSecurityAgency/ghidra/blob/master/Ghidra/Features/Decompiler/src/decompile/cpp/opbehavior.cc#L126

# https://htmlpreview.github.io/?https://github.com/NationalSecurityAgency/ghidra/blob/Ghidra_11.3.1_build/GhidraDocs/languages/html/sleigh.html
# https://htmlpreview.github.io/?https://github.com/NationalSecurityAgency/ghidra/blob/Ghidra_11.3.1_build/GhidraDocs/languages/html/pcoderef.html

import pypcode
from pypcode import OpCode
import kdrag as kd
import kdrag.smt as smt
import kdrag.theories.bitvec as bv
import operator

TRUE = smt.BitVecVal(1, 8)
FALSE = smt.BitVecVal(0, 8)

unop = {
    OpCode.COPY: lambda x: x,
    OpCode.INT_2COMP: operator.neg,
    OpCode.INT_NEGATE: operator.invert,
    OpCode.BOOL_NEGATE: lambda x: smt.If(x == TRUE, FALSE, TRUE),
}
binop = {
    OpCode.INT_ADD: operator.add,
    OpCode.INT_SUB: operator.sub,
    OpCode.INT_XOR: operator.xor,
    OpCode.INT_AND: operator.and_,
    OpCode.INT_OR: operator.or_,
    OpCode.INT_LEFT: operator.lshift,
    OpCode.INT_RIGHT: smt.LShR,
    OpCode.INT_SRIGHT: operator.rshift,
    OpCode.INT_MULT: operator.mul,
    OpCode.INT_DIV: smt.UDiv,
    OpCode.INT_REM: smt.URem,
    OpCode.INT_SDIV: operator.truediv,
    OpCode.INT_SREM: smt.SRem,
    OpCode.BOOL_XOR: lambda x, y: smt.If(x == y, FALSE, TRUE),
    OpCode.BOOL_AND: operator.and_,
    OpCode.BOOL_OR: operator.or_,
}


def test_pcode():
    ctx = pypcode.Context("x86:LE:64:default")
    # tx = ctx.translate(b"\x48\x35\x78\x56\x34\x12\xc3")

    tx = ctx.translate(b"\xf7\xd8")  # neg %eax
    for op in tx.ops:
        pass
