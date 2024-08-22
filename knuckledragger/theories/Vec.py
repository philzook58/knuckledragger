import knuckledragger as kd


Vec2 = kd.Record("Vec2", ("x", kd.R), ("y", kd.R))
u, v = kd.smt.Consts("u v", Vec2)
kd.notation.add.define([u, v], Vec2(u.x + v.x, u.y + v.y))
kd.notation.sub.define([u, v], Vec2(u.x - v.x, u.y - v.y))

norm2 = kd.define("norm2", [u], u.x * u.x + u.y * u.y)
