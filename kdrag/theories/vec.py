import kdrag as kd
import kdrag.smt as smt
import kdrag.theories.real as R
import functools

"""
Linear Algebra
"""
norm2 = kd.notation.SortDispatch(name="norm2")
dot = kd.notation.SortDispatch(name="dot")

Vec2 = kd.Struct("Vec2", ("x", kd.R), ("y", kd.R))
u, v = kd.smt.Consts("u v", Vec2)
kd.notation.add.define([u, v], Vec2(u.x + v.x, u.y + v.y))
kd.notation.sub.define([u, v], Vec2(u.x - v.x, u.y - v.y))

Vec2.vzero = Vec2(0, 0)  # type: ignore
Vec2.dot = dot.define([u, v], u.x * v.x + u.y * v.y)  # type: ignore
Vec2.norm2 = norm2.define([u], dot(u, u))  # type: ignore


Vec2.norm_pos = kd.prove(  # type: ignore
    kd.smt.ForAll([u], norm2(u) >= 0), by=[Vec2.norm2.defn, Vec2.dot.defn]
)
Vec2.norm_zero = kd.prove(  # type: ignore
    kd.smt.ForAll([u], (norm2(u) == 0) == (u == Vec2.vzero)),
    by=[Vec2.norm2.defn, Vec2.dot.defn],
)

dist = kd.define("dist", [u, v], R.sqrt(norm2(u - v)))


# Vec2.triangle = norm2(u - v) <= norm2(u) + norm2(v)
@functools.cache
def Vec(N):
    V = kd.Struct("Vec" + str(N), *[("x" + str(i), kd.R) for i in range(N)])
    u, v, w = kd.smt.Consts("u v w", V)
    kd.notation.getitem.register(V, lambda x, i: V.accessor(0, i)(x))
    kd.notation.add.define([u, v], V(*[u[i] + v[i] for i in range(N)]))
    kd.notation.sub.define([u, v], V(*[u[i] - v[i] for i in range(N)]))
    kd.notation.mul.define([u, v], V(*[u[i] * v[i] for i in range(N)]))
    kd.notation.div.define([u, v], V(*[u[i] / v[i] for i in range(N)]))
    kd.notation.neg.define([u], V(*[-u[i] for i in range(N)]))
    norm2.define([u], sum(u[i] * u[i] for i in range(N)))
    dot.define([u, v], sum(u[i] * v[i] for i in range(N)))
    return V


class VecTheory:
    def __init__(self, V):
        self.V = V
        add = kd.notation.add[V]
        sub = kd.notation.sub[V]
        neg = kd.notation.neg[V]
        u, v, w = smt.Consts("u v w", V)
        self.add_comm = kd.prove(u + v == v + u, by=[add.defn])
        self.add_assoc = kd.prove((u + v) + w == u + (v + w), by=[add.defn])
        # self.add_zero = kd.prove(u + V.zero == u, by=[add.defn])
        # self.add_neg = kd.prove(u + -u == V.zero, by=[add.defn])
        self.add_neg = kd.prove(u - v == u + -v, by=[add.defn, neg.defn, sub.defn])


Vec3 = Vec(3)  # kd.Struct("Vec3", ("x", kd.R), ("y", kd.R), ("z", kd.R))
u, v = kd.smt.Consts("u v", Vec3)
kd.notation.add.define([u, v], Vec3(u.x0 + v.x0, u.x1 + v.x1, u.x2 + v.x2))
kd.notation.sub.define([u, v], Vec3(u.x0 - v.x0, u.x1 - v.x1, u.x2 - v.x2))
norm2.define([u], u.x0 * u.x0 + u.x1 * u.x1 + u.x2 * u.x2)

cross = kd.define(
    "cross",
    [u, v],
    Vec3(
        u.x1 * v.x2 - u.x2 * v.x1, u.x2 * v.x0 - u.x0 * v.x2, u.x0 * v.x1 - u.x1 * v.x0
    ),
)

# TODO: instability with respect to the `by` ordering. That's bad
cross_antisym = kd.prove(
    kd.smt.ForAll([u, v], cross(u, v) == -cross(v, u)),
    by=[kd.notation.neg[Vec3].defn, cross.defn],
)

# https://en.wikipedia.org/wiki/Vector_algebra_relations

# pythag = kd.prove(
#    kd.smt.ForAll([u, v], norm2(cross(u, v)) + dot(u, v) ** 2 == norm2(u) * norm2(v)),
#    by=[norm2[Vec3].defn, dot[Vec3].defn, cross.defn],
# )
ihat = Vec3(1, 0, 0)
jhat = Vec3(0, 1, 0)
khat = Vec3(0, 0, 1)
