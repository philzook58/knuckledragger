import kdrag as kd
from kdrag import QForAll, axiom
from kdrag.smt import Const, Consts, DeclareSort, Exists, ForAll, Function, Or

"""
https://en.wikipedia.org/wiki/Robinson_arithmetic

Robinson arithmetic is a weakening of Peano arithmetic without induction

"""

N = DeclareSort("N")

# helper variables
x, y, z = Consts("x y z", N)


# signature
zero = Const("zero", N)
succ = Function("succ", N, N)
add = Function("add", N, N, N)
mul = Function("mul", N, N, N)
kd.notation.add.register(N, add)
kd.notation.mul.register(N, mul)

succ_not_zero = axiom(ForAll([x], succ(x) != zero))
succ_inj = axiom(QForAll([x, y], succ(x) == succ(y), x == y))

# This axioms is a theorem in typical Peano arithmetic
zero_or_succ = axiom(ForAll([y], Or(y == zero, Exists([x], succ(x) == y))))

add_zero = axiom(ForAll([x], add(x, zero) == x))
add_succ = axiom(ForAll([x, y], add(x, succ(y)) == succ(add(x, y))))
mul_zero = axiom(ForAll([x], mul(x, zero) == zero))
mul_succ = axiom(ForAll([x, y], mul(x, succ(y)) == add(mul(x, y), x)))
