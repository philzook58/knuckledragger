from kdrag import Theorem, define
from kdrag.smt import And, ArraySort, Consts, ForAll, Lambda
import kdrag.theories.real as real

RFun = ArraySort(real.R, real.R)
f, g, h = Consts("f g h", RFun)
x, y, c = Consts("x y c", real.R)

smul = define("RFun.smul", [c, f], Lambda([x], real.mul(c, f[x])))


# TODO: if I leave these add and mul bare, I have problems in the following proofs. Not great. Z3 has bad handling of quantifiers + real operators
def Linear(f):
    return And(
        ForAll([x, y], f[real.add(x, y)] == real.add(f[x], f[y])),
        ForAll([x, c], f[real.mul(c, x)] == real.mul(c, f[x])),
    )


is_linear = define("is_linear", [f], Linear(f))


@Theorem(ForAll([f, g], is_linear(f), is_linear(g), is_linear(f + g)))
def linear_add(l):
    f, g = l.fixes()
    l.unfold()
    hf, hg = l.intro(), l.intro()
    l.andE(hf)
    l.andE(hg)
    l.split()

    _x, _y = l.fixes()
    l.simp()
    l.rw(0)
    l.rw(2)
    l.auto(unfold=[real.add])

    _x, _c = l.fixes()
    l.simp()
    l.rw(1)
    l.rw(3)
    l.auto(unfold=[real.mul])


@Theorem(ForAll([f, c], is_linear(f), is_linear(smul(c, f))))
def linear_smul(l):
    f, c = l.fixes()
    l.unfold()
    h = l.intro()
    l.split(at=h)
    l.split()

    _x, _y = l.fixes()
    l.simp()
    l.rw(0)
    l.auto(unfold=[real.add, real.mul])

    _x, _c2 = l.fixes()
    l.simp()
    l.rw(1)
    l.auto(unfold=[real.mul])
