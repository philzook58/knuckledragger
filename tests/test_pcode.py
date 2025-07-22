
from kdrag.all import *
from kdrag.contrib.pcode.asmspec import assemble_and_check_str, AsmSpec, run_all_paths, kd_macro
import pytest

@pytest.mark.slow
def test_42():
    with open("/tmp/knuckle.s", "w") as f:
        f.write(kd_macro)
        f.flush()
    ret_42 = """
    .include "/tmp/knuckle.s"
    .globl myfunc

    .text
        kd_entry myfunc "(assert true)"
        movq $42, %rax
        kd_assert my_assert "(assert (= RAX (_ bv42 64)))"
        kd_exit func_end "(assert (= RAX (_ bv42 64)))"
        ret
    """
    res = assemble_and_check_str(ret_42)
    assert len(res.successes) == 2, res.successes
    assert len(res.failures) == 0, res.failures
    
@pytest.mark.slow
def test_cmov():
    with open("/tmp/knuckle.s", "w") as f:
        f.write(kd_macro)
        f.flush()
    ret_42 = """
    .include "/tmp/knuckle.s"
    .globl  _start
    kd_entry _start "(assert true)"
            movq     %rdi, %rax
            cmp     %rdi, %rsi
            cmovb   %rsi, %rax
    kd_exit _start_end "(assert (= RAX (ite (bvult RDI RSI) RDI RSI)))"
    #kd_exit _start_end "(assert (or (= RAX RDI) (= RAX RSI)))"
            ret
    """
    res = assemble_and_check_str(ret_42)
    assert len(res.successes) == 2, res.successes
    assert len(res.failures) == 0, res.failures
