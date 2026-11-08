import kdrag as kd
from kdrag import QForAll, axiom
from kdrag.smt import And, Const, Consts, DeclareSort, ForAll, Function

N = DeclareSort("N")

# helper variables
x, y, z = Consts("x y z", N)

# https://en.wikipedia.org/wiki/Peano_axioms#Peano_arithmetic_as_first-order_theory

# signature
zero = Const("zero", N)
succ = Function("succ", N, N)
add = Function("add", N, N, N)
mul = Function("mul", N, N, N)
kd.notation.add.register(N, add)
kd.notation.mul.register(N, mul)

succ_not_zero = axiom(ForAll([x], succ(x) != zero))
succ_inj = axiom(QForAll([x, y], succ(x) == succ(y), x == y))
add_zero = axiom(ForAll([x], add(x, zero) == x))
add_succ = axiom(ForAll([x, y], add(x, succ(y)) == succ(add(x, y))))
mul_zero = axiom(ForAll([x], mul(x, zero) == zero))
mul_succ = axiom(ForAll([x, y], mul(x, succ(y)) == add(mul(x, y), x)))


def induct(ys, P) -> kd.Proof:
    return axiom(QForAll([ys], And(P(zero), QForAll([x], P(x), P(succ(x)))), P(ys)))


# zero_or_succ = kd.prove(
#    smt.ForAll([y], smt.Or(y == zero, smt.Exists([x], succ(x) == y))), by=[]
# )
