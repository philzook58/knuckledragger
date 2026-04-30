import kdrag as kd
import kdrag.smt as smt
import kdrag.contrib.nand2tetris as nt
from kdrag.contrib.nand2tetris import ainsn, Jmp, Dest, Comp, cinsn, step
from kdrag.smt import ForAll, Exists, Implies, And, Or, Not, If, IntVal, Const, BitVecVal  # noqa: F401
from kdrag import prove, axiom, Theorem  # noqa: F401
st = Const("st", nt.Nand2State)



prog1 = [ainsn(47)]
prove(step(nt.init_state(prog1)).A == 47, unfold=[step])

prog2 = [cinsn(Dest.A, Comp.ONE), 
         cinsn(Dest.M, Comp.A)]
#print([bin(p) for p in prog2])
st = step(step(nt.init_state(prog2)))
prove(st.A == 1, unfold=[step])
prove(st.ram[1] == 1, unfold=[step])
#print(kd.full_simp(st.ram))
#assert kd.full_simp(st.A).eq(BitVecVal(1, 16))

