
from kdrag.all import *
from kdrag.contrib.pcode.asmspec import assemble_and_check_str, AsmSpec, run_all_paths, kd_macro
import kdrag.contrib.pcode as pcode

import pytest
import subprocess


def check_code(asm, nsucc, nfail):
    with open("/tmp/knuckle.s", "w") as f:
        f.write(kd_macro)
        f.flush()
    res = assemble_and_check_str(asm)
    assert len(res.successes) == nsucc, res.successes
    assert len(res.failures) == nfail, res.failures


@pytest.mark.slow
def test_42():
    ret_42 = r"""
    .include "/tmp/knuckle.s"
    .globl myfunc

    .text
        kd_entry myfunc "true"
        movq $42, %rax
        kd_assert my_assert "(= RAX (_ bv42 64))"
        kd_exit func_end "(= %rax (_ bv42 64))"
        ret
    """
    check_code(ret_42, 2, 0)


@pytest.mark.slow
def test_prelude():
    code = """
    .include "/tmp/knuckle.s"
    .globl myfunc
    kd_prelude "(define-const my42 (_ BitVec 64) (_ bv42 64))"

    .text
        kd_entry myfunc "true"
        movq $42, %rax
        kd_exit func_end "(= RAX my42)"
        ret
    """
    check_code(code, 1, 0)

@pytest.mark.slow
def test_assign():
    code = """
    .include "/tmp/knuckle.s"
    .globl myfunc
    kd_prelude "(declare-const mytemp (_ BitVec 64))"

    .text
        kd_entry myfunc "true"
        movq $42, %rax
        kd_assign mylabel mytemp "(bvadd RAX (_ bv1 64))"
        kd_exit func_end "(= mytemp (_ bv43 64))"
        ret
    """
    check_code(code, 1, 0)

@pytest.mark.slow
def test_cmov():
    ret_42 = """
    .include "/tmp/knuckle.s"
    .globl  _start
    kd_entry _start "true"
            movq     %rdi, %rax
            cmp     %rdi, %rsi
            cmovb   %rsi, %rax
    kd_exit _start_end "(= RAX (ite (bvult RDI RSI) RDI RSI))"
    #kd_exit _start_end "(or (= RAX RDI) (= RAX RSI))"
            ret
    """
    check_code(ret_42, 2, 0)


@pytest.mark.slow
def test_mem():
    ret_42 = """
.include "/tmp/knuckle.s"
.global  _start
kd_entry _start "true"
    movq     $42, (%rsp)
kd_exit _start_end "(= (select ram RSP) (_ bv42 8))"
    ret
    """
    check_code(ret_42, 1, 0)
    # wrong value in mem
    ret_42 = """
.include "/tmp/knuckle.s"
.global  _start
kd_entry _start "true"
    movq     $42, (%rsp)
kd_exit _start_end "(= (select ram RSP) (_ bv43 8))"
    ret
    """
    check_code(ret_42, 0, 1)

        # wrong addr
    ret_42 = """
.include "/tmp/knuckle.s"
.global  _start
kd_entry _start "true"
    movq     $42, (%rsp)
kd_exit _start_end "(= (select ram (bvadd RSP (_ bv1 64))) (_ bv43 8))"
    ret
    """
    check_code(ret_42, 0, 1)

@pytest.mark.slow
def test_mem64():
    code = """
.include "/tmp/knuckle.s"
.global  _start
kd_entry _start "true"
    movq     $12345678, (%rsp)
kd_exit _start_end "(= (select ram64 RSP) (_ bv12345678 64))"
    ret
    """
    check_code(code, 1, 0)


@pytest.mark.slow
def test_cut():
    code = """
.include "/tmp/knuckle.s"
.global  _start
kd_entry _start "true"
    movq     $42, %rdi
kd_cut mycut "(= RDI (_ bv42 64))"
    jmp mycut
    """
    check_code(code, 2, 0)


@pytest.mark.slow
def test_cli():
    code = """
    .include "/tmp/knuckle.s"
    .globl myfunc

    .text
        kd_entry myfunc "true"
        movq $42, %rax
        kd_exit func_end "(= RAX (_ bv42 64))"
        ret
    """
    with open("/tmp/mov42.s", "w") as f:
        f.write(code)
        f.flush()
    res = subprocess.run("python3 -m kdrag.contrib.pcode /tmp/mov42.s", shell=True, check=True, capture_output=True, text=True)
    assert "verification conditions passed! ✅✅✅✅" in res.stdout

    res = subprocess.run("python3 -m kdrag.contrib.pcode /tmp/mov42.s --max_insns 1", shell=True, capture_output=True, text=True)
    assert "[❌] OutOfGas()" in res.stdout

    code = """
    .include "/tmp/knuckle.s"
    .globl myfunc

    .text
        kd_entry myfunc "true"
        movq $42, %rax
        kd_exit func_end "(= RAX (_ bv43 64))"
        ret
    """
    with open("/tmp/mov42.s", "w") as f:
        f.write(code)
        f.flush()
    res = subprocess.run("python3 -m kdrag.contrib.pcode /tmp/mov42.s", shell=True, capture_output=True, text=True)
    assert "verification conditions failed. ❌❌❌❌" in res.stdout

@pytest.mark.slow
def test_riscv32():
    code = """
    .include "/tmp/knuckle.s"
        .text
        .globl  myfunc
    kd_entry myfunc, "true"
        addi    sp, sp, -4       # make room on the stack
        li      t0, 42           # t0 ← 42
        sw      t0, 0(sp)        # [sp] = 42
    kd_exit myfunc_end,  "(= (select ram32 sp) (_ bv42 32))"
        ret
    """
    with open("/tmp/mov42.s", "w") as f:
        f.write(code)
        f.flush()
    res = subprocess.run("""nix-shell -p pkgsCross.riscv32-embedded.buildPackages.gcc \
        --run "riscv32-none-elf-as /tmp/mov42.s -o /tmp/mov42.o" """, shell=True, check=True, capture_output=True, text=True)


@pytest.mark.slow
def test_riscv32_write():
    code = """
    .include "/tmp/knuckle.s"
    .option norvc
    .text
    .globl _start
    _start:
kd_entry myfunc, "true"
    li   t0, 42          # load immediate 42 into t0
    li   t1, 1000        # load address 1000 into t1
    sw   t0, 0(t1)       # store t0 at memory address

kd_exit myfunc_end, "(select write (_ bv1000 32))"
    ret
    """
    with open("/tmp/mov42.s", "w") as f:
        f.write(code)
        f.flush()
    res = subprocess.run("""nix-shell -p pkgsCross.riscv32-embedded.buildPackages.gcc \
        --run "riscv32-none-elf-as /tmp/mov42.s -o /tmp/mov42.o" """, shell=True, check=True, capture_output=True, text=True)
    ctx = pcode.BinaryContext("/tmp/mov42.o", langid="RISCV:LE:32:default")
    spec = AsmSpec.of_file("/tmp/mov42.s", ctx)
    vcs = run_all_paths(ctx, spec)
    assert len(vcs) == 1
    for vc in vcs:
        vc.verify(ctx)