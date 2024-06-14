"""
Defines an algebraic datatype for the Peano natural numbers and useful functions and properties.
"""

from z3 import Datatype, ForAll, And, Implies, Consts, If, Function, IntSort, Ints
from knuckledragger import axiom, lemma

Z = IntSort()
x, y = Ints("x y")


Nat = Datatype("Nat")
"""Nat = succ(pred Nat) | zero)"""
Nat.declare("zero")
Nat.declare("succ", ("pred", Nat))
Nat = Nat.create()


n, m, k = Consts("n m k", Nat)


def induct(P):
    """An induction axiom schema for natural numbers."""
    return axiom(
        Implies(
            And(P(Nat.zero), ForAll([n], Implies(P(n), P(Nat.succ(n))))),
            # -----------------------------------------------------------
            ForAll([n], P(n)),
        ),
        ("nat_induction", P),
    )


reify = Function("reify", Nat, Z)
# """reify  Nat  Z maps a natural number to the built in Z3 integers"""
reify_def = axiom(
    ForAll([n], reify(n) == If(Nat.is_zero(n), 0, reify(Nat.pred(n)) + 1))
)


reflect = Function("reflect", Z, Nat)
# """reflect  Z  Nat maps an integer to a natural number"""
reflect_def = axiom(
    ForAll([x], reflect(x) == If(x <= 0, Nat.zero, Nat.succ(reflect(x - 1))))
)

reflect_reify = lemma(
    ForAll([n], reflect(reify(n)) == n),
    by=[reflect_def, reify_def, induct(lambda n: reflect(reify(n)) == n)],
)

reify_ge_0 = lemma(
    ForAll([n], reify(n) >= 0), by=[reify_def, induct(lambda n: reify(n) >= 0)]
)

zero_homo = lemma(reify(Nat.zero) == 0, by=[reify_def])

succ_homo = lemma(
    ForAll([n], reify(Nat.succ(n)) == 1 + reify(n)),
    by=[reify_def, induct(lambda n: reify(Nat.succ(n)) == 1 + reify(n))],
)


add = Function("add", Nat, Nat, Nat)
add_def = axiom(
    ForAll([n, m], add(n, m) == If(Nat.is_zero(n), m, Nat.succ(add(Nat.pred(n), m))))
)
