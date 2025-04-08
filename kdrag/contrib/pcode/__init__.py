# Ghidra emulator

# https://github.com/NationalSecurityAgency/ghidra/blob/master/Ghidra/Features/Decompiler/src/decompile/cpp/emulate.cc
# https://github.com/NationalSecurityAgency/ghidra/blob/master/Ghidra/Features/Decompiler/src/decompile/cpp/opbehavior.cc#L126

# https://htmlpreview.github.io/?https://github.com/NationalSecurityAgency/ghidra/blob/Ghidra_11.3.1_build/GhidraDocs/languages/html/sleigh.html
# https://htmlpreview.github.io/?https://github.com/NationalSecurityAgency/ghidra/blob/Ghidra_11.3.1_build/GhidraDocs/languages/html/pcoderef.html

import pypcode
from pypcode import OpCode
import cle

import kdrag as kd
import kdrag.smt as smt
import kdrag.theories.bitvec as bv
import operator
from dataclasses import dataclass

TRUE = smt.BitVecVal(1, 8)
FALSE = smt.BitVecVal(0, 8)

BV8 = smt.BitVecSort(8)
BV64 = smt.BitVecSort(64)

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
    OpCode.INT_NOTEQUAL: lambda x, y: smt.If(x != y, TRUE, FALSE),
    OpCode.INT_EQUAL: lambda x, y: smt.If(x == y, TRUE, FALSE),
    OpCode.INT_CARRY: lambda x, y: smt.If(
        smt.Not(smt.BVAddNoOverflow(x, y, signed=False)), TRUE, FALSE
    ),
    OpCode.INT_SCARRY: lambda x, y: smt.If(
        smt.Not(smt.BVAddNoOverflow(x, y, signed=True)), TRUE, FALSE
    ),
    OpCode.INT_SBORROW: lambda x, y: smt.If(
        smt.Not(smt.BVSubNoOverflow(x, y)), TRUE, FALSE
    ),
    OpCode.INT_SLESS: lambda x, y: smt.If(x < y, TRUE, FALSE),
    OpCode.INT_SLESSEQUAL: lambda x, y: smt.If(x <= y, TRUE, FALSE),
    OpCode.INT_LESS: lambda x, y: smt.If(smt.ULT(x, y), TRUE, FALSE),
    OpCode.INT_LESSEQUAL: lambda x, y: smt.If(smt.ULE(x, y), TRUE, FALSE),
    OpCode.BOOL_AND: operator.and_,
    OpCode.BOOL_OR: operator.or_,
}

MemSort = smt.ArraySort(
    smt.BitVecSort(64), smt.BitVecSort(8)
)  # TODO: Architectures may not be 64 bit
"""Memory is modelled as an array of 64-bit addresses to 8-bit values"""

MemStateSort = kd.Struct(
    "MemState", ("ram", MemSort), ("register", MemSort), ("unique", MemSort)
)


@dataclass
class _TestVarnode:
    space: str
    offset: int
    size: int


@dataclass
class MemState:
    """
    MemState is a wrapper that offers getvalue and setvalue methods

    #>>> mem.getvalue(_TestVarnode("ram", 0, 8))
    #>>> mem.setvalue(_TestVarnode("ram", 0, 8), 1)
    >>> mem = MemState(smt.Array("mymem", BV64, BV8))

    """

    mem: smt.DatatypeRef

    @classmethod
    def Const(cls, name: str):
        return MemState(smt.Const(name, MemStateSort))

    def getvalue(self, vnode: pypcode.Varnode) -> smt.BitVecRef | int:
        if vnode.space.name == "const":
            return vnode.offset
        else:
            mem = getattr(self.mem, vnode.space.name)
            if mem is None:
                raise ValueError(f"Unknown memory space: {vnode.space.name}")
            return bv.SelectConcat(mem, smt.BitVecVal(vnode.offset, 64), vnode.size)

    def setvalue(self, vnode: pypcode.Varnode, value: smt.BitVecRef):
        assert vnode.space.name != "const"
        return MemState(
            self.mem._replace(
                **{
                    vnode.space.name: bv.StoreConcat(
                        getattr(self.mem, vnode.space.name),
                        smt.BitVecVal(vnode.offset, 64),
                        value,
                    )
                }
            )
        )

    def getvalue_ram(self, offset: smt.BitVecRef | int, size: int) -> smt.BitVecRef:
        return bv.SelectConcat(self.mem.ram, offset, size)

    def setvalue_ram(self, offset: smt.BitVecRef | int, value: smt.BitVecRef):
        return MemState(
            self.mem._replace(ram=bv.StoreConcat(self.mem.ram, offset, value))  # type: ignore
        )


# Pure Operations


def executeUnary(op: pypcode.PcodeOp, memstate: MemState) -> MemState:
    assert op.output is not None
    in1 = memstate.getvalue(op.inputs[0])
    out = unop[op.opcode](in1)
    return memstate.setvalue(op.output, out)


def executeBinary(op: pypcode.PcodeOp, memstate: MemState) -> MemState:
    assert op.output is not None
    in1 = memstate.getvalue(op.inputs[0])
    in2 = memstate.getvalue(op.inputs[1])
    out = binop[op.opcode](in1, in2)
    return memstate.setvalue(op.output, out)


def executeSignExtend(op: pypcode.PcodeOp, memstate: MemState) -> MemState:
    assert op.output is not None
    in1 = memstate.getvalue(op.inputs[0])
    out = smt.SignExt((op.output.size - op.inputs[0].size) * 8, in1)
    return memstate.setvalue(op.output, out)


def executeSubpiece(op: pypcode.PcodeOp, memstate: MemState) -> MemState:
    assert op.output is not None
    in1 = memstate.getvalue(op.inputs[0])
    assert op.inputs[1].space.name == "const"
    offset = op.inputs[1].offset * 8
    out = smt.Extract(op.output.size * 8 + offset - 1, offset, in1)
    assert out.size() == op.output.size * 8
    return memstate.setvalue(op.output, out)


def executePopcount(op: pypcode.PcodeOp, memstate: MemState) -> MemState:
    assert op.output is not None
    in1 = memstate.getvalue(op.inputs[0])
    out = smt.BitVecVal(0, op.inputs[0].size * 8)
    for i in range(op.inputs[0].size * 8):
        out += (in1 >> i) & 1
    outsize = op.output.size * 8
    insize = op.inputs[0].size * 8
    if outsize > insize:
        out = smt.ZeroExt(outsize - insize, out)
    elif outsize < insize:
        out = smt.Extract(outsize - 1, 0, out)
    assert out.size() == outsize
    return memstate.setvalue(op.output, out)


def executeLoad(op: pypcode.PcodeOp, memstate: MemState) -> MemState:
    assert op.output is not None
    off = memstate.getvalue(op.inputs[1])  # offset to load from
    spc = memstate.getvalue(op.inputs[0])  # memory space
    return memstate.setvalue(op.output, memstate.getvalue_ram(off, op.output.size))


def executeStore(op: pypcode.PcodeOp, memstate: MemState) -> MemState:
    val = memstate.getvalue(op.inputs[2])  # value being stored
    assert isinstance(val, smt.BitVecRef)
    off = memstate.getvalue(op.inputs[1])  # offset to store at
    spc = memstate.getvalue(op.inputs[0])  # memory space
    return memstate.setvalue_ram(off, val)


def executeCBranch(op, memstate: MemState) -> smt.BoolRef | bool:
    cond = memstate.getvalue(op.inputs[1])
    return cond != 0


PC = tuple[int, int]  # (address, pcode_pc)


def pc_of_addr(addr: int) -> PC:
    return (addr, 0)


def pretty_insn(insn: pypcode.Instruction) -> str:
    return f"{insn.addr.offset:#x}/{insn.length}: {insn.mnem} {insn.body}"


pypcode.Instruction.__repr__ = pretty_insn  # type: ignore


def pretty_op(op: pypcode.PcodeOp) -> str:
    return pypcode.PcodePrettyPrinter.fmt_op(op)


pypcode.PcodeOp.__repr__ = pretty_op  # type: ignore


class BinaryContext:
    def __init__(self, filename):
        self.pcode_cache = {}
        self.insn_cache = {}
        self.filename = filename
        self.loader = cle.loader.Loader(filename)
        self.bin_hash = None
        self.ctx = pypcode.Context("x86:LE:64:default")  # TODO: derive from cle

    def disassemble(self, addr):
        if addr in self.insn_cache:
            return self.insn_cache[addr]
        memory = self.loader.memory.load(addr, 0x128)  # 128 bytes? good enough?
        insns = self.ctx.disassemble(memory, addr, 0).instructions
        assert len(insns) > 0
        for insn in insns:
            self.insn_cache[insn.addr.offset] = insn
        return self.insn_cache[addr]

    def translate(self, addr):
        if addr in self.pcode_cache:
            return self.pcode_cache[addr]
        insn = self.disassemble(addr)
        memory = self.loader.memory.load(addr, insn.length)
        ops = self.ctx.translate(memory, base_address=addr, offset=0).ops
        assert len(ops) > 0
        self.pcode_cache[addr] = ops
        return ops

    def executeInsn(self, memstate, addr): ...

    def executeCurrentOp(self, op, memstate: MemState, pc: PC) -> tuple[MemState, PC]:
        opcode = op.opcode
        if opcode == pypcode.OpCode.IMARK:
            return memstate, self.fallthruOp(pc)
        elif opcode == pypcode.OpCode.LOAD:
            return executeLoad(op, memstate), self.fallthruOp(pc)
        elif opcode == pypcode.OpCode.STORE:
            return executeStore(op, memstate), self.fallthruOp(pc)
        elif opcode == pypcode.OpCode.BRANCH:
            return memstate, self.executeBranch(op, pc)
        elif opcode == pypcode.OpCode.CBRANCH:
            cond = executeCBranch(op, memstate)
            (addr1, pcode_pc1) = self.executeBranch(op, pc)
            (addr2, pcode_pc2) = self.fallthruOp(pc)
            return memstate, (
                smt.If(cond, addr1, addr2),
                smt.If(cond, pcode_pc1, pcode_pc2),
            )
        elif opcode == pypcode.OpCode.INT_SEXT:
            return executeSignExtend(op, memstate), self.fallthruOp(pc)
        elif opcode == pypcode.OpCode.SUBPIECE:
            return executeSubpiece(op, memstate), self.fallthruOp(pc)
        elif opcode == pypcode.OpCode.POPCOUNT:
            return executePopcount(op, memstate), self.fallthruOp(pc)
        elif opcode in unop:
            return executeUnary(op, memstate), self.fallthruOp(pc)
        elif opcode in binop:
            return executeBinary(op, memstate), self.fallthruOp(pc)
        else:
            raise NotImplementedError("Opcode not implemented: ", op.opcode)

    def fallthruOp(self, pc: PC):
        addr, pcode_pc = pc
        pcode_pc += 1
        if pcode_pc >= len(self.translate(addr)):
            addr += self.disassemble(addr).length
            return (addr, 0)
        else:
            return (addr, pcode_pc)

    def executeBranch(self, op: pypcode.PcodeOp, pc: PC) -> PC:
        addr, pcode_pc = pc
        destaddr = op.inputs[0]
        if destaddr.space.name == "const":
            pcode_pc += destaddr.offset
            if pcode_pc == len(self.translate(addr)):
                return self.fallthruOp((addr, pcode_pc))
            elif pcode_pc < 0 or pcode_pc >= len(self.translate(addr)):
                raise ValueError(
                    f"Lowlevel Error. Bad intra-instruction branch: {pcode_pc}"
                )
            else:
                return (addr, pcode_pc)
        elif destaddr.space.name == "ram":
            return (destaddr.offset, 0)
        else:
            raise ValueError(f"Unknown branch target: {destaddr.space.name}")

    def sym_execute(self, memstate: MemState, addr: int, max_insns=1):
        pc0: PC = (addr, 0)
        todo = [(memstate, pc0, max_insns, [])]
        res = []
        while todo:
            memstate, pc, max_insns, path_cond = todo.pop()
            op = self.translate(pc[0])[pc[1]]
            memstate1, pc1 = self.executeCurrentOp(op, memstate, pc)
            if isinstance(pc1[0], smt.ExprRef):
                assert isinstance(pc1[1], smt.ExprRef)
                for vaddr, vpcode_pc in kd.utils.all_values(pc1[0], pc1[1]):
                    assert isinstance(vaddr, smt.IntNumRef) and isinstance(
                        vpcode_pc, smt.IntNumRef
                    )
                    addr, pcode_pc = vaddr.as_long(), vpcode_pc.as_long()
                    if pc[0] != addr:
                        max_insns -= 1
                    pc = (addr, pcode_pc)
                    path_cond1 = path_cond + [pc1[0] == addr, pc1[1] == pcode_pc]
                    if max_insns > 0:
                        todo.append((memstate, pc, max_insns, path_cond1))
                    else:
                        res.append((memstate, pc, path_cond1))
            else:
                if pc[0] != pc1[0]:
                    max_insns -= 1
                if max_insns > 0:
                    todo.append((memstate1, pc1, max_insns, path_cond))  # type: ignore
                else:
                    res.append((memstate1, pc1, path_cond))
        return res


def test_pcode():
    ctx = pypcode.Context("x86:LE:64:default")
    # tx = ctx.translate(b"\x48\x35\x78\x56\x34\x12\xc3")

    tx = ctx.translate(b"\xf7\xd8")  # neg %eax
    for op in tx.ops:
        pass
