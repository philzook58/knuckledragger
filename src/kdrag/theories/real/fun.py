import kdrag as kd
import kdrag.smt as smt
import kdrag.theories.real as real

RFun = smt.ArraySort(real.R, real.R)
f, g, h = smt.Consts("f g h", RFun)
x, y, c = smt.Consts("x y c", real.R)

smul = kd.define("smul", [c, f], smt.Lambda([x], real.mul(c, f[x])))


# TODO: if I leave these add and mul bare, I have problems. Hmm.
def Linear(f):
    return smt.And(
        smt.ForAll([x, y], f[real.add(x, y)] == real.add(f[x], f[y])),
        smt.ForAll([x, c], f[real.mul(c, x)] == real.mul(c, f[x])),
    )


is_linear = kd.define("is_linear", [f], Linear(f))


@kd.Theorem(smt.ForAll([f, g], is_linear(f), is_linear(g), is_linear(f + g)))
def linear_add(l):
    f, g = l.fixes()
    l.unfold()
    _h = l.intros()
    l.split(at=-1)
    l.split(at=-1)
    l.split(at=0)
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


@kd.Theorem(smt.ForAll([f, c], is_linear(f), is_linear(smul(c, f))))
def linear_smul(l):
    f, c = l.fixes()
    l.unfold()
    _h = l.intros()
    l.split(at=-1)  # Fix this. giving h doesn't work
    l.split()

    _x, _y = l.fixes()
    l.simp()
    l.rw(0)
    l.auto(unfold=[real.add, real.mul])

    _x, _c2 = l.fixes()
    l.simp()
    l.rw(1)
    l.auto(unfold=[real.mul])
