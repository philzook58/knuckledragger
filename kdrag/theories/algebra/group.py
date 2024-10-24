import kdrag as kd
import kdrag.smt as smt

G = smt.DeclareSort("G")
mul = smt.Function("mul", G, G, G)
kd.notation.mul.register(G, mul)
e = smt.Const("e", G)
inv = smt.Function("inv", G, G)
x, y, z = smt.Consts("x y z", G)

mul_id = kd.axiom(smt.ForAll([x], x * e == x))
inv_mul = kd.axiom(smt.ForAll([x], inv(x) * x == x))
mul_assoc = kd.axiom(smt.ForAll([x, y, z], x * (y * z) == (x * y) * z))
