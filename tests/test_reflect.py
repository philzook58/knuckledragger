import kdrag as kd
import kdrag.smt as smt
import kdrag.reflect


BV32 = smt.BitVecSort(32)
PC = kd.Enum("PC", ["mycpy", "loop", "done"])
State = kd.Struct("State49032", ("pc", PC), ("ram", smt.ArraySort(BV32, smt.BitVecSort(8))), ("len", BV32), ("src", BV32), ("dst", BV32))


@kdrag.reflect.reflect
def step(st : State) -> State:
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
    
def test_reflect():
    assert True