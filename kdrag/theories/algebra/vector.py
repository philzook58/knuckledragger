import kdrag as kd
import kdrag.smt as smt

# https://en.wikipedia.org/wiki/Vector_space

V = smt.DeclareSort("V")
u, v, w = smt.Consts("u v w", V)

add = smt.Function("add", V, V, V)
kd.notation.add.register(V, add)

add_comm = kd.axiom(smt.ForAll([u, v], u + v == v + u))
add_assoc = kd.axiom(smt.ForAll([u, v, w], u + (v + w) == (u + v) + w))

zero = smt.Const("zero", V)

add_zero = kd.axiom(smt.ForAll([u], u + zero == u))
zero_add = kd.lemma(smt.ForAll([u], zero + u == u), by=[add_comm, add_zero])

smul = smt.Function("smul", V, smt.RealSort(), V)
kd.notation.mul.register(V, smul)
x, y = smt.Reals("x y")

smul_one = kd.axiom(smt.ForAll([u], u * 1 == u))
