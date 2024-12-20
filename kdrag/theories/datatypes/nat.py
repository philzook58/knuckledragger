"""
Defines an algebraic datatype for the Peano natural numbers and useful functions and properties.
"""

from kdrag.smt import (
    Datatype,
    ForAll,
    And,
    Implies,
    Consts,
    If,
    Function,
    IntSort,
    Ints,
)
import kdrag as kd
from kdrag import axiom, lemma, define
import kdrag.smt as smt
import kdrag.notation as notation

Nat = kd.Inductive("Nat")
Nat.declare("Z")
Nat.declare("S", ("pred", Nat))
Nat = Nat.create()


n, m, k = smt.Consts("n m k", Nat)
x, y, z = smt.Consts("x y z", Nat)

add = smt.Function("add", Nat, Nat, Nat)
add = kd.define("add", [x, y], smt.If(x.is_Z, y, Nat.S(add(x.pred, y))))
kd.notation.add.register(Nat, add)

add_z_l = kd.kernel.lemma(smt.ForAll([x], add(Nat.Z, x) == x), by=[add.defn])
add_s_l = kd.kernel.lemma(
    smt.ForAll([x, y], add(Nat.S(x), y) == Nat.S(add(x, y))), by=[add.defn]
)

_l = kd.Lemma(smt.ForAll([x], add(x, Nat.Z) == x))
print(_l)
_x = _l.fixes()
_l.induct(_x)
_l.auto(by=[add.defn])
a = _l.intros()
_l.auto(by=[add.defn])
add_x_zero = _l.qed()

l = kd.Lemma(smt.ForAll([x], add(x, Nat.Z) == x))
_x1 = l.intros()
l.induct(_x1)
l.auto(by=[add.defn])
l.auto(by=[add.defn])
add_Z_r = l.qed()

l = kd.Lemma(smt.ForAll([x, y], add(x, Nat.S(y)) == Nat.S(add(x, y))))
_x1, _y1 = l.intros()
l.induct(_x1)
l.rw(add.defn)
l.simp()
l.rw(add.defn)
l.simp()
l.auto()
_z1 = l.fixes()
l.auto(by=[add.defn])
add_s_r = l.qed()

l = kd.Lemma(smt.ForAll([x, y], add(x, y) == add(y, x)))
_x1, _y1 = l.intros()
l.induct(_x1)
l.auto(by=[add.defn, add_Z_r])
_z1 = l.fixes()
l.auto(by=[add.defn, add_s_r])
add_comm = l.qed()

l = kd.Lemma(smt.ForAll([x, y, z], add(x, add(y, z)) == add(add(x, y), z)))
_x1, _y1, _z1 = l.intros()
l.induct(_x1)
l.rw(add_z_l)
l.rw(add_z_l)
l.auto()
l.auto(by=[add.defn, add_comm])
add_assoc = l.qed()

"""
Z = smt.IntSort()
x, y = smt.Ints("x y")
def induct(P):
    return axiom(
        Implies(
            And(P(Nat.zero), ForAll([n], Implies(P(n), P(Nat.succ(n))))),
            # -----------------------------------------------------------
            ForAll([n], P(n)),
        ),
        ("nat_induction", P),
    )


reify = Function("reify", Nat, Z)
# reify  Nat  Z maps a natural number to the built in smt integers
reify_def = axiom(
    ForAll([n], reify(n) == If(Nat.is_zero(n), 0, reify(Nat.pred(n)) + 1))
)


reflect = Function("reflect", Z, Nat)
# reflect  Z  Nat maps an integer to a natural number
# reflect_def = axiom(
#    ForAll([x], reflect(x) == If(x <= 0, Nat.zero, Nat.succ(reflect(x - 1))))
# )
reflect = define("reflect", [x], If(x <= 0, Nat.zero, Nat.succ(reflect(x - 1))))

reflect_reify = lemma(
    ForAll([n], reflect(reify(n)) == n),
    by=[reflect.defn, reify_def, induct(lambda n: reflect(reify(n)) == n)],
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

notation.add.register(Nat, add)

add = Function("add", Nat, Nat, Nat)
add = kd.notation.add.define([n, m], If(n.is_zero, m, Nat.succ(add(n.pred, m))))
add_0_n = kd.kernel.lemma(ForAll([n], Nat.zero + n == n), by=[add.defn])
"""
