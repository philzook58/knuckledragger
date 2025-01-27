import kdrag as kd
import kdrag.smt as smt

# https://en.wikipedia.org/wiki/Group_(mathematics)

G = smt.DeclareSort("G")
mul = smt.Function("mul", G, G, G)
kd.notation.mul.register(G, mul)
e = smt.Const("e", G)
inv = smt.Function("inv", G, G)
x, y, z = smt.Consts("x y z", G)

mul_assoc = kd.axiom(smt.ForAll([x, y, z], x * (y * z) == (x * y) * z))
id_left = kd.axiom(smt.ForAll([x], e * x == x))
inv_left = kd.axiom(smt.ForAll([x], inv(x) * x == e))

c = kd.Calc([x], e, assume=[smt.ForAll([y], y * x == y)])
c.eq(e * x)
c.eq(x, by=[id_left])
id_unique1 = c.qed()

c = kd.Calc([x], x * inv(x))
c.eq(e * (x * inv(x)), by=[id_left])
c.eq((inv(inv(x)) * inv(x)) * (x * inv(x)), by=[inv_left])
c.eq(inv(inv(x)) * ((inv(x) * x) * inv(x)), by=[mul_assoc])
c.eq(inv(inv(x)) * (e * inv(x)), by=[inv_left])
c.eq(inv(inv(x)) * inv(x), by=[id_left])
c.eq(e, by=[inv_left])
inv_right = c.qed()

c = kd.Calc([x], x * e)
c.eq(x * (inv(x) * x), by=[inv_left])
c.eq((x * inv(x)) * x, by=[mul_assoc])
c.eq(e * x, by=[inv_right])
c.eq(x, by=[id_left])
id_right = c.qed()

# c = kd.Calc([x], e, assume=[smt.ForAll([y], x * y == y)])
# c.eq(x * e)
# c.eq(x, by=[id_right])
# id_unique2 = c.qed()
l = kd.Lemma(kd.QForAll([x], kd.QForAll([y], x * y == y), x == e))
_x = l.fix()
l.intros()
l.eq(_x * e)
l.eq(_x, by=[id_right(_x)])
id_unique2 = l.qed()

c = kd.Calc([x, y], y, assume=[y * x == e])
c.eq(y * e, by=[id_right])
c.eq(y * (x * inv(x)), by=[inv_right])
c.eq((y * x) * inv(x), by=[mul_assoc])
c.eq(e * inv(x), by=[inv_right])
c.eq(inv(x), by=[id_left])
inv_unique1 = c.qed()


abelian = kd.define("abelian", [], smt.ForAll([x, y], x * y == y * x))
