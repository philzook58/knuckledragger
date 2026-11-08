import kdrag.theories.algebra.group as group
import kdrag as kd
from kdrag import axiom, prove
import kdrag.smt as smt
from kdrag.smt import Consts, DeclareSort, ForAll, Function
import kdrag.contrib.junk_drawer.generic as generic

# https://isabelle.in.tum.de/library/HOL/HOL/Lattices.html


class SemiLattice(generic.TypeClass):
    key: smt.SortRef
    idem: kd.Proof

    def check(self, T):
        self.Group = group.AbelSemiGroup(T)
        x, y, z = Consts("x y z", T)
        assert kd.utils.alpha_eq(self.idem.thm, ForAll([x], x * x == x))
        self.left_idem = prove(
            ForAll([x, y], x * (x * y) == x * y), by=[self.idem, self.Group.assoc]
        )
        self.right_idem = prove(
            ForAll([x, y], (y * x) * x == y * x), by=[self.idem, self.Group.assoc]
        )


L = DeclareSort("AbstractLattice")
x, y, z = Consts("x y z", L)
mul = Function("mul", L, L, L)
kd.notation.mul.register(L, mul)
assoc = axiom(ForAll([x, y, z], x * (y * z) == (x * y) * z))
comm = axiom(ForAll([x, y], x * y == y * x))
idem = axiom(ForAll([x], x * x == x))
group.Semigroup.register(L, assoc=assoc)
group.AbelSemiGroup.register(L, comm=comm)
SemiLattice.register(L, idem=idem)
