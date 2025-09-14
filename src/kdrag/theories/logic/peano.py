import kdrag as kd
import kdrag.smt as smt

N = smt.DeclareSort("N")

# helper variables
x, y, z = smt.Consts("x y z", N)

# https://en.wikipedia.org/wiki/Peano_axioms#Peano_arithmetic_as_first-order_theory

# signature
zero = smt.Const("zero", N)
succ = smt.Function("succ", N, N)
add = smt.Function("add", N, N, N)
mul = smt.Function("mul", N, N, N)
kd.notation.add.register(N, add)
kd.notation.mul.register(N, mul)

succ_not_zero = kd.axiom(smt.ForAll([x], succ(x) != zero))
succ_inj = kd.axiom(kd.QForAll([x, y], succ(x) == succ(y), x == y))
add_zero = kd.axiom(smt.ForAll([x], add(x, zero) == x))
add_succ = kd.axiom(smt.ForAll([x, y], add(x, succ(y)) == succ(add(x, y))))
mul_zero = kd.axiom(smt.ForAll([x], mul(x, zero) == zero))
mul_succ = kd.axiom(smt.ForAll([x, y], mul(x, succ(y)) == add(mul(x, y), x)))


def induct(ys, P) -> kd.Proof:
    return kd.axiom(
        kd.QForAll([ys], smt.And(P(zero), kd.QForAll([x], P(x), P(succ(x)))), P(ys))
    )


# zero_or_succ = kd.prove(
#    smt.ForAll([y], smt.Or(y == zero, smt.Exists([x], succ(x) == y))), by=[]
# )
