# Ghidra emulator

# https://github.com/NationalSecurityAgency/ghidra/blob/master/Ghidra/Features/Decompiler/src/decompile/cpp/emulate.cc
# https://github.com/NationalSecurityAgency/ghidra/blob/master/Ghidra/Features/Decompiler/src/decompile/cpp/opbehavior.cc#L126

# https://htmlpreview.github.io/?https://github.com/NationalSecurityAgency/ghidra/blob/Ghidra_11.3.1_build/GhidraDocs/languages/html/sleigh.html
# https://htmlpreview.github.io/?https://github.com/NationalSecurityAgency/ghidra/blob/Ghidra_11.3.1_build/GhidraDocs/languages/html/pcoderef.html

import pypcode
from pypcode import OpCode
import cle
import archinfo

import kdrag as kd
import kdrag.smt as smt
import kdrag.theories.bitvec as bv
import operator
from dataclasses import dataclass
from typing import Optional, NamedTuple

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

_possible_bits = [8, 16, 32, 64]

BV = {bits: smt.BitVecSort(bits) for bits in _possible_bits}

MemSorts = {
    bits: smt.ArraySort(smt.BitVecSort(bits), smt.BitVecSort(8))
    for bits in _possible_bits
}
"""Memory is modelled as an array of 64-bit addresses to 8-bit values"""

MemStateSort = {
    bits: kd.Struct(
        "MemState", ("ram", MemSort), ("register", MemSort), ("unique", MemSort)
    )
    for bits, MemSort in MemSorts.items()
}


@dataclass
class _TestVarnode:
    space: str
    offset: int
    size: int


class MemState(NamedTuple):
    """
    MemState is a wrapper that offers getvalue and setvalue methods

    #>>> mem.getvalue(_TestVarnode("ram", 0, 8))
    #>>> mem.setvalue(_TestVarnode("ram", 0, 8), 1)
    >>> mem = MemState.Const("mymem") #(smt.Array("mymem", BV[64], BV[8]), bits=64)

    """

    ram: smt.ArrayRef
    register: smt.ArrayRef
    unique: smt.ArrayRef
    bits: int  # bitwidth of addresses
    read: smt.ArrayRef
    # write: smt.ArrayRef
    write: list[tuple[smt.BitVecRef, int]]

    @classmethod
    def Const(cls, name: str, bits: int = 64) -> "MemState":
        mem = smt.Const(name, MemStateSort[bits])
        return MemState(
            ram=mem.ram,
            register=mem.register,
            unique=mem.unique,
            bits=bits,
            read=smt.Array(name + "_read", BV[bits], smt.BoolSort()),
            write=[],  # smt.Array(name + "_write", BV[bits], smt.BoolSort()),
        )

    def to_expr(self) -> smt.DatatypeRef:
        return MemStateSort[self.bits].mk(
            ram=self.ram, register=self.register, unique=self.unique
        )

    def getvalue(self, vnode: pypcode.Varnode) -> smt.BitVecRef | int:
        if vnode.space.name == "const":
            return smt.BitVecVal(vnode.offset, vnode.size * 8)
        else:
            if vnode.space.name == "ram":
                mem = self.ram
            elif vnode.space.name == "register":
                mem = self.register
            elif vnode.space.name == "unique":
                mem = self.unique
            else:
                raise ValueError(f"Unknown memory space: {vnode.space.name}")
            return bv.SelectConcat(
                mem, smt.BitVecVal(vnode.offset, self.bits), vnode.size
            )

    def setvalue(self, vnode: pypcode.Varnode, value: smt.BitVecRef):
        offset = smt.BitVecVal(vnode.offset, self.bits)
        space = vnode.space.name
        if space == "ram":
            return self.setvalue_ram(offset, value)
        elif space == "register":
            return self.set_register(vnode.offset, value)
        elif space == "unique":
            return self._replace(unique=bv.StoreConcat(self.unique, offset, value))
        else:
            raise ValueError(f"Unknown memory space: {space}")

    def set_register(self, offset: smt.BitVecRef | int, value: smt.BitVecRef):
        # This is mainly for the purpose of manually setting PC in evaluator loop
        if not isinstance(offset, smt.BitVecRef):
            offset1 = smt.BitVecVal(offset, self.bits)
        else:
            offset1 = offset
        return self._replace(
            register=bv.StoreConcat(
                self.register,
                smt.BitVecVal(offset1, self.bits),
                value,
            )
        )

    def getvalue_ram(self, offset: smt.BitVecRef | int, size: int) -> smt.BitVecRef:
        # TODO: update read?
        return bv.SelectConcat(self.ram, offset, size)

    def setvalue_ram(self, offset: smt.BitVecRef | int, value: smt.BitVecRef):
        if not isinstance(offset, smt.BitVecRef):
            offset1 = smt.BitVecVal(offset, self.bits)
        else:
            offset1 = offset
        return self._replace(
            ram=bv.StoreConcat(self.ram, offset1, value),
            write=self.write + [(offset1, value.size())],  # fun.MultiStore(
            #     self.write, offset1, *([smt.BoolVal(True)] * value.size())
            # ),
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


def executeZeroExtend(op: pypcode.PcodeOp, memstate: MemState) -> MemState:
    assert op.output is not None
    in1 = memstate.getvalue(op.inputs[0])
    out = smt.ZeroExt((op.output.size - op.inputs[0].size) * 8, in1)
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
    if op.inputs[0].space.name != "const":
        raise ValueError(
            f"Expected constant space in LOAD, got {op.inputs[0].space.name}, {pretty_op(op)}"
        )
    return memstate.setvalue(op.output, memstate.getvalue_ram(off, op.output.size))


def executeStore(op: pypcode.PcodeOp, memstate: MemState) -> MemState:
    val = memstate.getvalue(op.inputs[2])  # value being stored
    assert isinstance(val, smt.BitVecRef)
    off = memstate.getvalue(op.inputs[1])  # offset to store at
    # TODO: check if space is the "ram" space
    # assert op.inputs[0].space.name == "const",
    return memstate.setvalue_ram(off, val)


def executeCBranch(op, memstate: MemState) -> smt.BoolRef | bool:
    cond = memstate.getvalue(op.inputs[1])
    return cond != 0


type PC = tuple[int, int]  # (address, pcode_pc)


def pc_of_addr(addr: int) -> PC:
    return (addr, 0)


def pretty_insn(insn: pypcode.Instruction) -> str:
    return f"{insn.addr.offset:#x}/{insn.length}: {insn.mnem} {insn.body}"


pypcode.Instruction.__repr__ = pretty_insn  # type: ignore


def pretty_op(op: pypcode.PcodeOp) -> str:
    return pypcode.PcodePrettyPrinter.fmt_op(op)


pypcode.PcodeOp.__repr__ = pretty_op  # type: ignore


@dataclass
class SimState:
    memstate: MemState
    pc: PC
    path_cond: list[smt.BoolRef]


class BinaryContext:
    """
    Almost all operations one wants to do on assembly are dependent on the binary and where it was loaded.
    BinaryContext is a class that holds the binary and provides methods to disassemble and translate instructions.
    It is the analog of an angr `Project` in some respects.

    Run `python3 -m pypcode --list` to see available langid.
    - RISCV:LE:64:default
    """

    def __init__(self, filename=None, langid="x86:LE:64:default"):
        self.pcode_cache = {}
        self.insn_cache = {}
        self.filename = None
        self.loader = None
        self.bin_hash = hash((filename, langid))
        ainfo = archinfo.ArchPcode(langid)
        self.pc: tuple[int, int] = ainfo.registers[
            "pc"
        ]  # TODO: handle different archs? Or will "pc" always work?
        self.bits = ainfo.bits
        assert self.bits == self.pc[1] * 8
        self.memory_endness = ainfo.memory_endness  # TODO
        self.register_endness = ainfo.register_endness  # TODO
        self.ctx = pypcode.Context(langid)  # TODO: derive from cle

        # Defintions that are used but may need to be unfolded
        self.definitions: list[smt.FuncDeclRef] = list(bv.select64_le.values())
        self.definitions.extend(bv.select64_be.values())
        self.definitions.extend(bv.select32_le.values())
        self.definitions.extend(bv.select32_be.values())
        if filename is not None:
            self.load(filename)

    def load(self, main_binary, **kwargs):
        """
        Load a binary file and initialize the context.
        """
        self.filename = main_binary
        self.loader = cle.loader.Loader(main_binary, **kwargs)
        # self.ctx = pypcode.Context(self.loader.arch.name) # TODO: derive from cle
        # Note: These decls need to be synchronized with the code in BinaryContext.substitute
        # The decls are used for parsing textual smtlib
        # substitute is used to convert these names into memstate expressions
        decls = {
            name: smt.BitVec(name, vnode.size * 8)
            for name, vnode in self.ctx.registers.items()
        }
        # support %reg names
        decls.update(
            {
                "%" + name.lower(): smt.BitVec("%" + name.lower(), vnode.size * 8)
                for name, vnode in self.ctx.registers.items()
            }
        )
        decls["ram"] = smt.Array("ram", smt.BitVecSort(self.bits), smt.BitVecSort(8))
        for b in _possible_bits:
            decls[f"ram{b}"] = smt.Array(
                f"ram{b}", smt.BitVecSort(self.bits), smt.BitVecSort(b)
            )
        self.state_vars = decls
        self.pcode_cache.clear()
        self.insn_cache.clear()

    def disassemble(self, addr):
        if addr in self.insn_cache:
            return self.insn_cache[addr]
        assert self.loader is not None, (
            "BinaryContext must be loaded before disassembling"
        )
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
        assert self.loader is not None, (
            "BinaryContext must be loaded before disassembling"
        )
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
        elif opcode == pypcode.OpCode.INT_ZEXT:
            return executeZeroExtend(op, memstate), self.fallthruOp(pc)
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

    def execute1(self, memstate: MemState, pc: PC) -> tuple[MemState, PC]:
        """
        Execute a single PCode instruction at addr, returning the new memstate and pc.
        """
        addr = pc[0]
        op = self.translate(addr)[pc[1]]
        return self.executeCurrentOp(op, memstate, pc)

    def execute1_schema(self, pc: PC) -> kd.Proof:
        """
        For a given concrete PC and binary, we can generate an axiomatic description of how execution
        of a single instruction at that PC will change the memory state and program counter.
        """
        assert (
            isinstance(pc, tuple)
            and len(pc) == 2
            and isinstance(pc[0], int)
            and isinstance(pc[1], int)
        )
        argsorts = [
            smt.IntSort(),  # hash of context
            MemStateSort,  # memstate
            smt.IntSort(),  # address
            smt.IntSort(),  # pcode_pc
        ]
        next_pcode_pc = smt.Function(
            "next_pcode_pc",
            *argsorts,
            smt.IntSort(),
        )
        next_addr = smt.Function("next_addr", *argsorts, smt.IntSort())
        next_mem = smt.Function(
            "next_mem",
            *argsorts,
            MemStateSort,
        )
        mem = MemState.Const("mem")
        mem1, pc1 = self.execute1(mem, pc)
        mem, mem1 = mem.to_expr(), mem1.to_expr()
        execute_ax = kd.axiom(
            smt.ForAll(
                [mem],
                smt.And(
                    next_mem(
                        self.bin_hash,
                        mem,
                        pc[0],
                        pc[1],
                    )
                    == mem1,
                    next_addr(
                        self.bin_hash,
                        mem,
                        pc[0],
                        pc[1],
                    )
                    == pc1[0],
                    next_pcode_pc(
                        self.bin_hash,
                        mem,
                        pc[0],
                        pc[1],
                    )
                    == pc1[1],
                ),
            )
        )

        return execute_ax

    def sym_execute(
        self,
        memstate: MemState,
        addr: int,
        path_cond: Optional[list[smt.BoolRef]] = None,
        max_insns=1,
        breakpoints=[],
        verbose=False,
    ) -> list[SimState]:
        """
        Symbolically execute a real instruction at addr, returning a list of SimState objects.
        A single instruction may contain multiple Pcode instructions or even pcode loops.
        Hence a symbolic execution may be required for even a single instruction.
        """
        pc0: tuple[int, int] = (addr, 0)
        if path_cond is None:
            path_cond = []
        todo: list[tuple[MemState, PC, int, list[smt.BoolRef]]] = [
            (memstate, pc0, max_insns, path_cond)
        ]
        res = []
        while todo:
            memstate, pc, max_insns, path_cond = todo.pop()
            if verbose:
                print(
                    f"Executing {pretty_insn(self.disassemble(pc[0]))} at {pc} PCODE {pretty_op(self.translate(pc[0])[pc[1]])}"
                )
            memstate1, pc1 = self.execute1(memstate, pc)
            if isinstance(
                pc1[0], smt.ExprRef
            ):  # PC has become symbolic, requiring branching
                assert isinstance(pc1[1], smt.ExprRef)
                s = smt.Solver()
                s.add(path_cond)
                s.add(
                    pc1[0] == smt.FreshConst(pc1[0].sort())
                )  # To seed them in the model
                s.add(pc1[1] == smt.FreshConst(pc1[1].sort()))
                while s.check() != smt.unsat:
                    m = s.model()  # smt.unknown should crash
                    vaddr, vpcode_pc = m.eval(pc1[0]), m.eval(pc1[1])
                    s.add(
                        smt.Not(smt.And(pc1[0] == vaddr, pc1[1] == vpcode_pc))
                    )  # outlaw this model for next example
                    addr, pcode_pc = vaddr.as_long(), vpcode_pc.as_long()
                    assert isinstance(addr, int) and isinstance(pcode_pc, int)
                    if pcode_pc == 0:
                        max_insns1 = max_insns - 1
                        # pcode does not have explicit PC updates, but we want them
                        memstate2 = memstate1.set_register(
                            self.pc[0], smt.BitVecVal(addr, self.pc[1] * 8)
                        )
                    else:
                        max_insns1 = max_insns
                        memstate2 = memstate1
                    next_pc = (addr, pcode_pc)
                    path_cond1 = path_cond + [pc1[0] == vaddr, pc1[1] == vpcode_pc]
                    if addr in breakpoints:
                        res.append(SimState(memstate2, next_pc, path_cond1))
                    elif max_insns1 <= 0:
                        res.append(SimState(memstate2, next_pc, path_cond1))
                    else:
                        todo.append((memstate2, next_pc, max_insns1, path_cond1))
            else:  # PC is concrete
                if (
                    pc1[1] == 0
                ):  # pcode_pc == 0 means we are at the start of an instruction. Kind of. There are some edge cases, TODO
                    max_insns -= 1
                    # pcode does not have explicit PC updates, but we want them
                    memstate1 = memstate1.set_register(
                        self.pc[0], smt.BitVecVal(pc1[0], self.pc[1] * 8)
                    )
                if pc1[0] in breakpoints:
                    res.append(SimState(memstate1, pc1, path_cond))
                elif max_insns <= 0:
                    res.append(SimState(memstate1, pc1, path_cond))
                else:
                    todo.append((memstate1, pc1, max_insns, path_cond))  # type: ignore
        return res

    def get_reg(self, memstate: MemState, regname: str) -> smt.BitVecRef:
        """
        Get the value of a register from the memstate.

        >>> ctx = BinaryContext()
        >>> memstate = MemState.Const("test_mem")
        >>> memstate = ctx.set_reg(memstate, "RAX", smt.BitVec("RAX", 64))
        >>> ctx.get_reg(memstate, "RAX")
        RAX
        """
        vnode = self.ctx.registers[regname]
        return smt.simplify(memstate.getvalue(vnode))

    def set_reg(
        self, memstate: MemState, regname: str, value: smt.BitVecRef
    ) -> MemState:
        """
        Set the value of a register in the memstate.
        """
        vnode = self.ctx.registers[regname]
        return memstate.setvalue(vnode, value)

    def init_mem(self) -> MemState:
        """
        Initialize the memory state with empty memory.

        >>> ctx = BinaryContext()
        >>> memstate = ctx.init_mem()
        >>> ctx.get_reg(memstate, "RAX")
        RAX!...
        """
        memstate = MemState.Const("mem0", bits=self.bits)
        free_offset = 0
        for name, vnode in self.ctx.registers.items():
            # interestingness heuristic on length of name
            # and only store free space registers in order to speed up.
            if vnode.offset >= free_offset and len(name) <= 4:
                memstate = self.set_reg(
                    memstate,
                    name,
                    smt.FreshConst(smt.BitVecSort(vnode.size * 8), prefix=name),
                )
                free_offset = vnode.offset + vnode.size
        return memstate

    def get_regs(self, memstate: MemState) -> dict[str, smt.BitVecRef]:
        """
        Get the state of the registers from the memstate.
        """
        return {
            regname: self.get_reg(memstate, regname)
            for regname in self.ctx.registers.keys()
        }

    def substitute(self, memstate: MemState, expr: smt.ExprRef) -> smt.ExprRef:
        """
        Substitute the values in memstate into the expression `expr`.
        `expr` uses the short register names and `ram`
        """
        # Note: These substs need to be synchronized with the decls in BinaryContext.loads
        # Much faster typically to pull only those constants that are used in the expression
        # Hmm. This seems be quite slow again
        consts = {t.decl().name(): t for t in kd.utils.consts(expr)}
        substs: list[tuple[smt.ExprRef, smt.ExprRef]] = [
            (t, self.get_reg(memstate, regname))
            for regname, t in consts.items()
            if regname in self.ctx.registers
        ]
        # substitute in registers of form %reg
        substs.extend(
            [
                (t, self.get_reg(memstate, regname[1:].upper()))
                for regname, t in consts.items()
                if regname[0] == "%" and regname[1:].upper() in self.ctx.registers
            ]
        )
        if "ram" in consts:
            substs.append((smt.Array("ram", BV[self.bits], BV[8]), memstate.ram))
        for n in _possible_bits:
            ramn = f"ram{n}"
            if ramn in consts:
                addr = smt.BitVec("addr", self.bits)
                substs.append(
                    (
                        smt.Array(ramn, BV[self.bits], BV[n]),
                        smt.Lambda([addr], memstate.getvalue_ram(addr, n // 8)),
                    )
                )

        return smt.substitute(expr, *substs)

    # def state_lam(self, expr : smt.ExprRef) -> smt.QuantifierRef:
    #    mem =

    def unfold(self, expr: smt.ExprRef) -> smt.ExprRef:
        """
        Fully unpacked, the expressions are not readable. But definitions are opaque to z3 until unfolded.
        This unfolds helper definitions used during constraint production.

        >>> x = smt.BitVec("x", 64)
        >>> ctx = BinaryContext()
        >>> ctx.unfold(x)
        x
        >>> import kdrag.theories.bitvec as bv
        >>> ram = smt.Array("ram", BV[64], BV[8])
        >>> smt.simplify(ctx.unfold(bv.select64_le[16](ram, x)))
        Concat(ram[1 + x], ram[x])
        """
        return kd.kernel.unfold(expr, self.definitions)[0]

    def model_registers(
        self,
        model: smt.ModelRef,
        memstate: MemState,
    ) -> dict[str, smt.BitVecRef]:
        """
        Get values of all registers in model.
        """
        return {
            regname: model.eval(self.get_reg(memstate, regname))
            for regname in self.ctx.registers.keys()
        }


def test_pcode():
    ctx = pypcode.Context("x86:LE:64:default")
    # tx = ctx.translate(b"\x48\x35\x78\x56\x34\x12\xc3")

    tx = ctx.translate(b"\xf7\xd8")  # neg %eax
    for op in tx.ops:
        pass
