import kdrag as kd
import kdrag.theories.real as real

Vec2 = kd.Struct("Vec2", ("x", kd.R), ("y", kd.R))
u, v = kd.smt.Consts("u v", Vec2)
add = kd.notation.add.define([u, v], Vec2(u.x + v.x, u.y + v.y))
sub = kd.notation.sub.define([u, v], Vec2(u.x - v.x, u.y - v.y))
neg = kd.notation.neg.define([u], Vec2(-u.x, -u.y))


vzero = Vec2(0, 0)
dot = kd.define("dot", [u, v], u.x * v.x + u.y * v.y)
norm2 = kd.define("norm2", [u], dot(u, u))
norm = kd.define("norm", [u], real.sqrt(dot(u, u)))

norm_pos = kd.prove(  #
    kd.smt.ForAll([u], norm2(u) >= 0), by=[norm2.defn, dot.defn]
)
Vec2.norm_zero = kd.prove(
    kd.smt.ForAll([u], (norm2(u) == 0) == (u == vzero)),
    by=[norm2.defn, dot.defn],
)

dist = kd.define("dist", [u, v], real.sqrt(norm2(u - v)))
