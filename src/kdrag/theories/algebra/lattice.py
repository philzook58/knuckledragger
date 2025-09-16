import kdrag.theories.algebra.group as group
import kdrag as kd
import kdrag.smt as smt
import kdrag.contrib.junk_drawer.generic as generic

# https://isabelle.in.tum.de/library/HOL/HOL/Lattices.html


class SemiLattice(generic.TypeClass):
    key: smt.SortRef
    idem: kd.Proof

    def check(self, T):
        self.Group = group.AbelSemiGroup(T)
        x, y, z = smt.Consts("x y z", T)
        assert kd.utils.alpha_eq(self.idem.thm, smt.ForAll([x], x * x == x))
        self.left_idem = kd.prove(
            smt.ForAll([x, y], x * (x * y) == x * y), by=[self.idem, self.Group.assoc]
        )
        self.right_idem = kd.prove(
            smt.ForAll([x, y], (y * x) * x == y * x), by=[self.idem, self.Group.assoc]
        )


L = smt.DeclareSort("AbstractLattice")
x, y, z = smt.Consts("x y z", L)
mul = smt.Function("mul", L, L, L)
kd.notation.mul.register(L, mul)
assoc = kd.axiom(smt.ForAll([x, y, z], x * (y * z) == (x * y) * z))
comm = kd.axiom(smt.ForAll([x, y], x * y == y * x))
idem = kd.axiom(smt.ForAll([x], x * x == x))
group.Semigroup.register(L, assoc=assoc)
group.AbelSemiGroup.register(L, comm=comm)
SemiLattice.register(L, idem=idem)
