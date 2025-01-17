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
import kdrag.theories.int as int_
import functools

Nat = kd.Inductive("Nat")
Nat.declare("Z")
Nat.declare("S", ("pred", Nat))
Nat = Nat.create()


S = Nat.S
Z = Nat.Z
one = S(Z)
two = S(one)

n, m, k = smt.Consts("n m k", Nat)
x, y, z = smt.Consts("x y z", Nat)

safe_pred = kd.define("safe_pred", [n], smt.If(n.is_Z, Nat.Z, n.pred))

a = smt.Int("a")
from_int = smt.Function("from_int", smt.IntSort(), Nat)
from_int = kd.define("from_int", [a], If(a <= 0, Nat.Z, Nat.S(from_int(a - 1))))

to_int = smt.Function("to_int", Nat, smt.IntSort())
to_int = kd.define("to_int", [n], If(n.is_Z, smt.IntVal(0), 1 + to_int(n.pred)))

# Homomorphism. Todo the other homomorphisms
to_int_Z = kd.lemma(to_int(Nat.Z) == 0, by=[to_int.defn])
to_int_S = kd.lemma(smt.ForAll([n], to_int(S(n)) == 1 + to_int(n)), by=[to_int.defn])

l = kd.Lemma(ForAll([n], to_int(n) >= 0))
_n = l.fix()
l.induct(_n)
l.auto(by=[to_int.defn])
l.auto(by=[to_int.defn])
to_int_ge_0 = l.qed()

l = kd.Lemma(smt.ForAll([n], from_int(to_int(n)) == n))
_n = l.fix()
l.induct(_n)
l.auto(by=[from_int.defn, to_int.defn])
l.auto(by=[from_int.defn, to_int.defn])
from_to_int = l.qed()

l = kd.Lemma(smt.ForAll([a], to_int(from_int(a)) == smt.If(a <= 0, 0, a)))
_a = l.fix()
l.induct(_a)
l.auto(by=[from_int.defn, to_int.defn])
l.auto(by=[from_int.defn, to_int.defn])
l.auto(by=[from_int.defn, to_int.defn])
to_from_int = l.qed()

double = smt.Function("double", Nat, Nat)
double = kd.define("double", [n], smt.If(n.is_Z, Z, S(S(double(n.pred)))))

add = smt.Function("add", Nat, Nat, Nat)
add = kd.define("add", [x, y], smt.If(x.is_Z, y, Nat.S(add(x.pred, y))))
kd.notation.add.register(Nat, add)

add_Z = kd.kernel.lemma(smt.ForAll([x], add(Nat.Z, x) == x), by=[add.defn])
add_S = kd.kernel.lemma(
    smt.ForAll([x, y], add(Nat.S(x), y) == Nat.S(add(x, y))), by=[add.defn]
)


# Testing a different style of writing contained lemmas
def add_x_zero():
    """ForAll(x, add(x, Nat.Z) == x)"""
    _l = kd.Lemma(smt.ForAll([x], add(x, Z) == x))
    _x = _l.fix()
    _l.induct(_x)
    _l.auto(by=[add.defn])
    _a = _l.fix()
    _l.auto(by=[add.defn])
    return _l.qed()


add_x_zero = add_x_zero()


l = kd.Lemma(smt.ForAll([x], add(x, Nat.Z) == x))
_x1 = l.fix()
l.induct(_x1)
l.auto(by=[add.defn])
l.auto(by=[add.defn])
add_Z_r = l.qed()

l = kd.Lemma(smt.ForAll([x, y], add(x, Nat.S(y)) == Nat.S(add(x, y))))
_x1, _y1 = l.fixes()
l.induct(_x1)
l.rw(add.defn)
l.simp()
l.rw(add.defn)
l.simp()
l.auto()
_z1 = l.fix()
l.auto(by=[add.defn])
add_s_r = l.qed()

l = kd.Lemma(smt.ForAll([x, y], add(x, y) == add(y, x)))
_x1, _y1 = l.fixes()
l.induct(_x1)
l.auto(by=[add.defn, add_Z_r])
_z1 = l.fix()
l.auto(by=[add.defn, add_s_r])
add_comm = l.qed()

l = kd.Lemma(smt.ForAll([x, y, z], add(x, add(y, z)) == add(add(x, y), z)))
_x1, _y1, _z1 = l.fixes()
l.induct(_x1)
l.rw(add_Z)
l.rw(add_Z)
l.auto()
l.auto(by=[add.defn, add_comm])
add_assoc = l.qed()
