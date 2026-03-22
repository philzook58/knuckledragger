
import kdrag as kd
import kdrag.smt as smt
import kdrag.reflect
from kdrag.contrib.pcode.asmspec import assemble_and_check_str, AsmSpec, run_all_paths, kd_macro, Debug
import kdrag.contrib.pcode as pcode
import kdrag.contrib.pcode.asmspec as asmspec
import kdrag.theories.bitvec as bv
import pytest
import subprocess

BV32 = smt.BitVecSort(32)
PC = kd.Enum("PC1234", ["mycpy", "loop", "done"])
# TODO: consider making this a reflected struct?
State = kd.Struct("State3049", ("pc", PC), ("ram", smt.ArraySort(BV32, smt.BitVecSort(8))), ("len", BV32), ("src", BV32), ("dst", BV32))


@kd.reflect.reflect
def step123(st : State) -> State:
    if st.pc == PC.mycpy:
        if st.len == smt.BitVecVal(0, 32):
            return st._replace(pc = PC.done)
        else:
            return st._replace(pc = PC.loop)
    elif st.pc == PC.loop:
        st = st._replace(ram=smt.Store(st.ram, st.dst, st.ram[st.src]))
        st = st._replace(len=st.len-1)
        st = st._replace(src=st.src+1)
        st = st._replace(dst=st.dst+1)
        if st.len == 1:
            return st._replace(pc = PC.done)
        else:
            return st._replace(pc = PC.loop)
    elif st.pc == PC.done:
        return st
    else:
        return st #kd.Undef(State) # unreachable

trans_step = kd.trans(step123)

@pytest.mark.slow
def test_bisim():
    asm = """
        .text
        .globl mycpy
        .align 2

    # a0 is src
    # a1 is dst
    # a2 is len
    mycpy:
        beq a2, x0, .done
    .loop:
        lb t0, 0(a0)
        sb t0, 0(a1)
        addi a0, a0, 1
        addi a1, a1, 1
        addi a2, a2, -1
        bne a2, x0, .loop
    .done:
        ret
    """

    with open("/tmp/mov42.s", "w") as f:
        f.write(asm)
        f.flush()
    res = subprocess.run("""nix-shell -p pkgsCross.riscv32-embedded.buildPackages.gcc \
        --run "riscv32-none-elf-as /tmp/mov42.s -o /tmp/mov42.o" """, shell=True, check=True, capture_output=True, text=True)