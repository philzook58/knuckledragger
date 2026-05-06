import kdrag as kd
import kdrag.theories.real as real
from kdrag.smt import ForAll, Real
from kdrag import prove, define  # noqa: F401

Vec2 = kd.Struct("Vec2", ("x", kd.R), ("y", kd.R))
u, v = kd.smt.Consts("u v", Vec2)
add = kd.notation.add.define([u, v], Vec2(u.x + v.x, u.y + v.y))
sub = kd.notation.sub.define([u, v], Vec2(u.x - v.x, u.y - v.y))
neg = kd.notation.neg.define([u], Vec2(-u.x, -u.y))

r = Real("r")
smul = define("Vec2.smul", [r, u], Vec2(r * u.x, r * u.y))

vzero = Vec2(0, 0)
dot = kd.define("Vec2.dot", [u, v], u.x * v.x + u.y * v.y)
norm2 = kd.define("Vec2.norm2", [u], dot(u, u))
norm = kd.define("Vec2.norm", [u], real.sqrt(dot(u, u)))

norm2_pos = prove(ForAll([u], norm2(u) >= 0), by=[norm2.defn, dot.defn])
norm2_zero = prove(
    ForAll([u], (norm2(u) == 0) == (u == vzero)),
    by=[norm2.defn, dot.defn],
)

dist = define("Vec2.dist", [u, v], real.sqrt(norm2(u - v)))

cross = define("Vec2.cross", [u, v], u.x * v.y - u.y * v.x)
cross_self = prove(ForAll([u], cross(u, u) == 0), by=[cross.defn])
