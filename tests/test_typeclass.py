
import pytest
import kdrag.property as prop
import kdrag.contrib.junk_drawer.generic as generic
import kdrag as kd
import kdrag.smt as smt
class Foo1(generic.TypeClass):
    def check(self, key):
        assert self.x == 1

class Foo2(generic.TypeClass):
    def check(self, key):
        assert self.x == 2




def test_typeclass():
    Foo1.register("mykey", x=1)
    Foo2.register("mykey", x=2)
    Foo1("mykey")
    Foo2("mykey")
    with pytest.raises(Exception) as _:
        Foo1.register("mykey2", x=2)
    with pytest.raises(Exception) as _:
        Foo1.register("mykey", x=1)



def test_aci():
    T = smt.DeclareSort("ACISort")
    mul = smt.Function("mul", T, T, T) 
    kd.notation.mul.register(T, mul)
    x,y,z = smt.Consts("x y z", T)
    assoc = kd.axiom(smt.ForAll([x,y,z], (x * y) * z == x * (y * z)))
    comm = kd.axiom(smt.ForAll([x,y], x * y == y * x))

    generic.assoc.register(mul, assoc)
    generic.comm.register(mul, comm)
    trace = []
    t1 = x * ((x * y) * z)
    t2 = x * (x * (y * z))
    assert generic.assoc_norm(t1, trace=trace).eq(t2)
    kd.prove(t1 == t2, by=trace)
