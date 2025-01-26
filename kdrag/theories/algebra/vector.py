import kdrag as kd
import kdrag.smt as smt

# https://en.wikipedia.org/wiki/Vector_space

V = smt.DeclareSort("V")
u, v, w = smt.Consts("u v w", V)

add = smt.Function("vadd", V, V, V)
kd.notation.add.register(V, add)


add_comm = kd.axiom(smt.ForAll([u, v], u + v == v + u))
add_assoc = kd.axiom(smt.ForAll([u, v, w], u + (v + w) == (u + v) + w))

zero = smt.Const("zero", V)

add_zero = kd.axiom(smt.ForAll([u], u + zero == u))
zero_add = kd.prove(smt.ForAll([u], zero + u == u), by=[add_comm, add_zero])

smul = smt.Function("smul", V, smt.RealSort(), V)
kd.notation.mul.register(V, smul)
x, y = smt.Reals("x y")

smul_one = kd.axiom(smt.ForAll([u], u * 1 == u))


# Possible design for theories.
vadd = kd.notation.SortDispatch()
vadd_assoc = {V: add_assoc}
vadd_comm = {V: add_comm}

vzero = {V: zero}
vadd_zero = {V: add_zero}


class VectorTheory:
    def __init__(self, T):
        self.T = T
        self.vadd = vadd[T]
        self.vadd_assoc = vadd_assoc[V]
        self.vadd_comm = vadd_comm[V]
