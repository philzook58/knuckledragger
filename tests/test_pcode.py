
from kdrag.all import *
from kdrag.contrib.pcode.asmspec import assemble_and_check_str, AsmSpec, run_all_paths, kd_macro, Debug
import kdrag.contrib.pcode as pcode
import kdrag.contrib.pcode.asmspec as asmspec
import kdrag.theories.bitvec as bv
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

def riscv_as(code):
    with open("/tmp/mov42.s", "w") as f:
        f.write(code)
        f.flush()
    res = subprocess.run("""nix-shell -p pkgsCross.riscv32-embedded.buildPackages.gcc \
        --run "riscv32-none-elf-as /tmp/mov42.s -o /tmp/mov42.o" """, shell=True, check=True, capture_output=True, text=True)



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

@pytest.mark.slow
def test_debugger():
    code = """
    .include "/tmp/knuckle.s"
    .option norvc
    .text
    .globl _start
    _start:
    li   t0, 42          # load immediate 42 into t0
    li   t1, 1000        # load address 1000 into t1
    sw   t0, 0(t1)       # store t0 at memory address
    ret
    """
    riscv_as(code)
    ctx = pcode.BinaryContext("/tmp/mov42.o", langid="RISCV:LE:32:default")
    spec = AsmSpec.of_file("/tmp/mov42.s", ctx)
    d = Debug(ctx, spec)
    d.add_entry("_start")
    d.start()
    print(d.insn())
    print(d.addr())
    print(d.reg("t0"))
    assert d.reg("t0").eq(smt.BitVecVal(42,32))
    assert not d.reg("t1").eq(smt.BitVecVal(1000,32))
    d.step()
    assert d.reg("t1").eq(smt.BitVecVal(1000,32))
    d.step()
    assert d.ram(smt.BitVecVal(1000,32), 4).eq(smt.BitVecVal(42,32))


    
def test_s2n_simple():
    # https://github.com/awslabs/s2n-bignum/blob/main/x86/tutorial/simple.ml
    code = r"""
    _start:
    add    %rax,%rbx
    sub    %rax,%rbx
    done:
    """

    with open("/tmp/simple.s", "w") as f:
        f.write(code)
        f.flush()
    res = subprocess.run("as /tmp/simple.s -o /tmp/simple.o", shell=True, check=True, capture_output=True, text=True)
    ctx = pcode.BinaryContext("/tmp/simple.o")

    dbg = asmspec.Debug(ctx)
    pc,a,b = smt.BitVecs("pc a b", 64)
    rax = ctx.state_vars[r"%rax"]
    rbx = ctx.state_vars[r"%rbx"]
    rip = ctx.state_vars[r"%rip"]
    dbg.add_entry("_start", 
    #smt.ForAll([a, b],
    smt.And(
        rax == a,
        rbx == b,
        rip == pc
    )
    #)
    )

    num_insn = smt.Int("num_insn")
    # Yeaaa, I'm not sure it's worth adding in set rip
    dbg.add_exit("done",
    smt.And(
    rbx == b,
    rip == pc+6,
    num_insn == 2
    ))
    dbg.start()
    dbg.run()
    dbg.verify()

@pytest.mark.slow
def test_sumi32():
    # https://www.philipzucker.com/asm_verify4/
    code = """
    .text
    .globl sum_i32
    .align 2
# int32_t sum_i32(const int32_t* arr, uint32_t n)
sum_i32:
    mv      t0, a0          # t0 = arr (cursor)
    mv      t1, a1          # t1 = n   (remaining)
    li      a0, 0           # a0 = sum (return value)

    beqz    t1, .done       # if n == 0 -> return 0

.loop:
    lw      t2, 0(t0)       # t2 = *arr
    add     a0, a0, t2      # sum += *arr
    addi    t0, t0, 4       # arr++
    addi    t1, t1, -1      # n--
    bnez    t1, .loop       # keep going while n != 0

.done:
    ret
    """
    with open("/tmp/sum32.s", "w") as f:
        f.write(code)
        f.flush()
    res = subprocess.run("""nix-shell -p pkgsCross.riscv32-embedded.buildPackages.gcc \
        --run "riscv32-none-elf-as /tmp/sum32.s -o /tmp/sum32.o" """, shell=True, check=True, capture_output=True, text=True)

    BV32 = smt.BitVecSort(32)
    BV8 = smt.BitVecSort(8)
    sum_i32 = smt.Function('sum_i32', smt.ArraySort(BV32, BV8), BV32, BV32, BV32, BV32)
    mem = smt.Array('mem', BV32, smt.BitVecSort(8))
    n,addr,acc,res = smt.BitVecs('n addr acc res', 32)

    sum_i32 = kd.define("sum_i32", [mem, acc, addr, n],
        smt.If(n == 0,
            acc,
            sum_i32(mem, acc + bv.select_concat(mem, addr, 4, le=True), addr + 4, n - 1)
        )
    )
    ctx = pcode.BinaryContext("/tmp/sum32.o", langid="RISCV:LE:32:default")
    t1 = ctx.state_vars["t1"]
    t0 = ctx.state_vars["t0"]
    a0 = ctx.state_vars["a0"]
    a1 = ctx.state_vars["a1"]
    ram = ctx.state_vars["ram"]
    spec = asmspec.AsmSpec(ctx)
    N = smt.BitVec("N", 32) #2

    spec.add_entry('sum_i32', spec.find_label("sum_i32"), smt.And(a1 == N, addr == a0, res == sum_i32(ram, 0, addr, N), N >= 0, N <= 2))
    end_addr = 4*N + addr
    spec.add_cut(".loop", spec.find_label(".loop"), smt.And(res == sum_i32(ram, a0, t0, t1), 4*N + addr == 4*t1 + t0, t1 > 0, t1 <= N))

    spec.add_exit(".done", spec.find_label(".done"), a0 == res)

    pf = asmspec.AsmProofState(spec)
    for i in range(4):
        l = pf.lemma(i)
        l.auto(by=sum_i32.defn)
        l.qed()
        #pf.auto(i, by=[sum_i32.defn])
    pf.qed()
