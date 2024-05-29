from z3 import Datatype, ForAll, And, Implies, Consts
from knuckledragger import axiom, lemma

Nat = Datatype("Nat")
Nat.declare("zero")
Nat.declare("succ", ("pred", Nat))
Nat = Nat.create()
n, m, k = Consts("n m k", Nat)


def induct(P):
    return axiom(
        Implies(
            And(P(Nat.zero), ForAll([n], Implies(P(n), P(Nat.succ(n))))),
            # -----------------------------------------------------------
            ForAll([n], P(n)),
        ),
        ("nat_induction", P),
    )
