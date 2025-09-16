import kdrag as kd
import kdrag.smt as smt
import kdrag.theories.set as set_
import kdrag.contrib.junk_drawer.generic as generic

# https://leanprover-community.github.io/mathematics_in_lean/C10_Topology.html
# https://isabelle.in.tum.de/library/HOL/HOL/Topological_Spaces.html

open = kd.notation.SortDispatch(name="open")


class Topology(generic.TypeClass):
    key: smt.SortRef
    open_UNIV: kd.Proof
    open_Int: kd.Proof
    open_Union: kd.Proof

    def check(self, T):
        self.Set = set_.Set(T)
        SetSet = set_.Set(self.Set)
        A, B = smt.Consts("A B", self.Set)
        K = smt.Const("K", SetSet)
        print(self.open_UNIV.thm.eq(open(self.Set.full)))
        self.assert_eq(self.open_UNIV.thm, open(self.Set.full))
        self.assert_eq(
            self.open_Int.thm,
            kd.QForAll([A, B], open(A), open(B), open(A & B)),
        )
        self.assert_eq(
            self.open_Union.thm,
            kd.QForAll([K], kd.QForAll([A], K[A], open(A)), open(set_.BigUnion(K))),
        )
        self.closed = kd.define("closed", [A], open(~A))


# https://en.wikipedia.org/wiki/Sierpi%C5%84ski_space
Sierpinski = kd.Inductive("Sierpinski")
Sierpinski.declare("S0")
Sierpinski.declare("S1")
Sierp = Sierpinski.create()
SierpSet = set_.Set(Sierp)
A, B = smt.Consts("A B", SierpSet)
K = smt.Const("K", set_.Set(SierpSet))
Sierp.open = open.define(
    [A],
    smt.Or(
        A == SierpSet.empty,  # {}
        A == SierpSet.full,  # {0,1}
        A == smt.Store(SierpSet.empty, Sierp.S1, True),  # {1}
    ),
)
Sierp.open_UNIV = kd.prove(open(SierpSet.full), by=[Sierp.open.defn])
Sierp.open_Int = kd.prove(
    kd.QForAll([A, B], open(A), open(B), open(A & B)), by=[Sierp.open.defn]
)
Sierp.open_Union = kd.prove(
    kd.QForAll([K], kd.QForAll([A], K[A], open(A)), open(set_.BigUnion(K))),
    by=[Sierp.open.defn],
)
Topology.register(
    Sierp,
    open_UNIV=Sierp.open_UNIV,
    open_Int=Sierp.open_Int,
    open_Union=Sierp.open_Union,
)
