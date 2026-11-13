"""
Algebraic datatype for the Peano natural numbers
"""

import kdrag as kd
from kdrag import Theorem, define, exact, prove
from kdrag.smt import Consts, ForAll, Function, If, Int, IntSort, IntVal
import kdrag.theories.int as int_  # int is more primitive. We import it's induction principle here.

Nat = kd.Nat


S = Nat.S
Z = Nat.Z
one = S(Z)
two = S(one)

n, m, k = Consts("n m k", Nat)
x, y, z = Consts("x y z", Nat)

safe_pred = define("safe_pred", [n], If(n.is_Z, Nat.Z, n.pred))

a = Int("a")
from_int = Function("from_int", IntSort(), Nat)
from_int = define("from_int", [a], If(a <= 0, Nat.Z, Nat.S(from_int(a - 1))))

to_int = Function("to_int", Nat, IntSort())
to_int = define("to_int", [n], If(n.is_Z, IntVal(0), 1 + to_int(n.pred)))

# Homomorphism. Todo the other homomorphisms
to_int_Z = prove(to_int(Nat.Z) == 0, by=[to_int.defn])
to_int_S = prove(ForAll([n], to_int(S(n)) == 1 + to_int(n)), by=[to_int.defn])


@Theorem(ForAll(n, to_int(n) >= 0))
def to_int_ge_0(l):
    _n = l.fix()
    l.induct(_n)
    l.auto(by=[to_int.defn])
    l.auto(by=[to_int.defn])


@Theorem(ForAll(n, from_int(to_int(n)) == n))
def from_to_int(l):
    _n = l.fix()
    l.induct(_n)
    l.auto(by=[from_int.defn, to_int.defn])
    l.auto(by=[from_int.defn, to_int.defn])


@Theorem(ForAll(a, to_int(from_int(a)) == If(a <= 0, 0, a)))
def to_from_int(l):
    _a = l.fix()
    l.induct(_a, using=int_.induct)
    l.auto(by=[from_int.defn, to_int.defn])
    l.auto(by=[from_int.defn, to_int.defn])
    l.auto(by=[from_int.defn, to_int.defn])


double = Function("double", Nat, Nat)
double = define("double", [n], If(n.is_Z, Z, S(S(double(n.pred)))))

add = Function("Nat.add", Nat, Nat, Nat)
add = define("Nat.add", [x, y], If(x.is_Z, y, Nat.S(add(x.pred, y))))
kd.notation.add.register(Nat, add)

add_Z = kd.kernel.prove(ForAll([x], add(Nat.Z, x) == x), by=[add.defn])
add_S = kd.kernel.prove(
    ForAll([x, y], add(Nat.S(x), y) == Nat.S(add(x, y))), by=[add.defn]
)


@Theorem(ForAll(x, add(x, Nat.Z) == x))
def add_Z_r(l):
    _x1 = l.fix()
    l.induct(_x1)
    l.auto(by=[add.defn(Nat.Z, Nat.Z)])
    _pred = l.fix()
    l.auto(by=[add.defn(Nat.S(_pred), Nat.Z)])


add_x_zero = exact(ForAll(x, add(x, Z) == x), add_Z_r)


@Theorem(ForAll([x, y], add(x, Nat.S(y)) == Nat.S(add(x, y))))
def add_s_r(l):
    x, _ = l.fixes()
    l.induct(x)
    l.simp(unfold=True)
    l.auto()
    l.fix()
    l.auto(by=[add.defn])


@Theorem(ForAll([x, y], add(x, y) == add(y, x)))
def add_comm(l):
    x, _ = l.fixes()
    l.induct(x)
    l.auto(by=[add.defn, add_Z_r])
    l.fix()
    l.auto(by=[add.defn, add_s_r])


@Theorem(ForAll([x, y, z], add(x, add(y, z)) == add(add(x, y), z)))
def add_assoc(l):
    x, _, _ = l.fixes()
    l.induct(x)
    l.rw(add_Z)
    l.rw(add_Z)
    l.auto()
    l.auto(by=[add.defn, add_comm])
