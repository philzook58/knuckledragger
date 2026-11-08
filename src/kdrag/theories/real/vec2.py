import kdrag as kd
from kdrag import Struct, define, prove  # noqa: F401
import kdrag.theories.real as real
from kdrag.smt import Consts, ForAll, Real

Vec2 = Struct("Vec2", ("x", kd.R), ("y", kd.R))
u, v = Consts("u v", Vec2)
add = kd.notation.add.define([u, v], Vec2(u.x + v.x, u.y + v.y))
sub = kd.notation.sub.define([u, v], Vec2(u.x - v.x, u.y - v.y))
neg = kd.notation.neg.define([u], Vec2(-u.x, -u.y))

r = Real("r")
smul = define("Vec2.smul", [r, u], Vec2(r * u.x, r * u.y))

vzero = Vec2(0, 0)
dot = define("Vec2.dot", [u, v], u.x * v.x + u.y * v.y)
norm2 = define("Vec2.norm2", [u], dot(u, u))
norm = define("Vec2.norm", [u], real.sqrt(dot(u, u)))

norm2_pos = prove(ForAll([u], norm2(u) >= 0), by=[norm2.defn, dot.defn])
norm2_zero = prove(
    ForAll([u], (norm2(u) == 0) == (u == vzero)),
    by=[norm2.defn, dot.defn],
)

dist = define("Vec2.dist", [u, v], real.sqrt(norm2(u - v)))

cross = define("Vec2.cross", [u, v], u.x * v.y - u.y * v.x)
cross_self = prove(ForAll([u], cross(u, u) == 0), by=[cross.defn])
