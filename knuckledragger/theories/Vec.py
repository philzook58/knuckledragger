import knuckledragger as kd
import knuckledragger.theories.Real as R

norm2 = kd.notation.SortDispatch(name="norm2")
dot = kd.notation.SortDispatch(name="dot")

Vec2 = kd.Record("Vec2", ("x", kd.R), ("y", kd.R))
u, v = kd.smt.Consts("u v", Vec2)
kd.notation.add.define([u, v], Vec2(u.x + v.x, u.y + v.y))
kd.notation.sub.define([u, v], Vec2(u.x - v.x, u.y - v.y))

Vec2.vzero = Vec2(0, 0)
Vec2.dot = dot.define([u, v], u.x * v.x + u.y * v.y)
Vec2.norm2 = norm2.define([u], dot(u, u))


Vec2.norm_pos = kd.lemma(
    kd.smt.ForAll([u], norm2(u) >= 0), by=[Vec2.norm2.defn, Vec2.dot.defn]
)
Vec2.norm_zero = kd.lemma(
    kd.smt.ForAll([u], (norm2(u) == 0) == (u == Vec2.vzero)),
    by=[Vec2.norm2.defn, Vec2.dot.defn],
)

dist = kd.define("dist", [u, v], R.sqrt(norm2(u - v)))

# Vec2.triangle = norm2(u - v) <= norm2(u) + norm2(v)

Vec3 = kd.Record("Vec3", ("x", kd.R), ("y", kd.R), ("z", kd.R))
u, v = kd.smt.Consts("u v", Vec3)
kd.notation.add.define([u, v], Vec3(u.x + v.x, u.y + v.y, u.z + v.z))
kd.notation.sub.define([u, v], Vec3(u.x - v.x, u.y - v.y, u.z - v.z))

norm2.define([u], u.x * u.x + u.y * u.y + u.z * u.z)
