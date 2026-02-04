import kdrag as kd
import kdrag.theories.real as real
import kdrag.smt as smt

Vec3 = kd.Struct("Vec3", ("x", kd.R), ("y", kd.R), ("z", kd.R))
u, v, w = kd.smt.Consts("u v w", Vec3)
add = kd.notation.add.define([u, v], Vec3(u.x + v.x, u.y + v.y, u.z + v.z))
add_comm = kd.prove(
    kd.smt.ForAll([u, v], add(u, v) == add(v, u)),
    by=[add.defn],
)
add_assoc = kd.prove(
    kd.smt.ForAll([u, v, w], add(add(u, v), w) == add(u, add(v, w))),
    by=[add.defn],
)

sub = kd.notation.sub.define([u, v], Vec3(u.x - v.x, u.y - v.y, u.z - v.z))
neg = kd.notation.neg.define([u], Vec3(-u.x, -u.y, -u.z))
a, b = smt.Reals("a b")
smul = kd.define("smul", [a, u], Vec3(a * u.x, a * u.y, a * u.z))


smul_assoc = kd.prove(
    kd.smt.ForAll([a, b, u], smul(a * b, u) == smul(a, smul(b, u))),
    by=[smul.defn],
)
smul_distrib = kd.prove(
    kd.smt.ForAll([a, b, u], smul(a + b, u) == smul(a, u) + smul(b, u)),
    by=[smul.defn, add.defn],
)
smul_distrib_r = kd.prove(
    kd.smt.ForAll([a, u, v], smul(a, u + v) == smul(a, u) + smul(a, v)),
    by=[smul.defn, add.defn],
)


vzero = Vec3(0, 0, 0)
add_zero = kd.prove(
    kd.smt.ForAll([u], u + vzero == u),
    by=[add.defn],
)
zero_add = kd.prove(
    kd.smt.ForAll([u], vzero + u == u),
    by=[add_zero, add_comm],
)
neg_zero = kd.prove(
    kd.smt.ForAll([u], -vzero == vzero),
    by=[neg.defn],
)

e1 = Vec3(1, 0, 0)
e2 = Vec3(0, 1, 0)
e3 = Vec3(0, 0, 1)


dot = kd.define("dot", [u, v], u.x * v.x + u.y * v.y + u.z * v.z)
dot_comm = kd.prove(
    kd.smt.ForAll([u, v], dot(u, v) == dot(v, u)),
    by=[dot.defn],
)
dot_add = kd.prove(
    kd.smt.ForAll([u, v, w], dot(u, v + w) == dot(u, v) + dot(u, w)),
    by=[dot.defn, add.defn],
)
dot_smul = kd.prove(
    kd.smt.ForAll([a, u, v], dot(smul(a, u), v) == a * dot(u, v)),
    by=[dot.defn, smul.defn],
)

dot_expand = kd.prove(
    kd.smt.ForAll(
        [u], u == smul(dot(u, e1), e1) + smul(dot(u, e2), e2) + smul(dot(u, e3), e3)
    ),
    by=[smul.defn, add.defn, dot.defn],
)
dot_self_pos = kd.prove(
    kd.smt.ForAll([u], dot(u, u) >= 0),
    by=[dot.defn],
)

norm2 = kd.define("norm2", [u], dot(u, u))
norm2_pos = kd.prove(kd.smt.ForAll([u], norm2(u) >= 0), by=[norm2.defn, dot_self_pos])
norm2_add = kd.prove(
    kd.smt.ForAll([u, v], norm2(u + v) == norm2(u) + norm2(v) + 2 * dot(u, v)),
    by=[norm2.defn, dot.defn, add.defn],
)
norm = kd.define("norm", [u], real.sqrt(norm2(u)))

# unstable
# cauchy_schwarz2 = kd.prove(
#    kd.smt.ForAll([u, v], dot(u, v) * dot(u, v) <= norm2(u) * norm2(v)),
#    by=[dot.defn, norm2.defn, add.defn],
# )


#    by=[norm2.defn, dot.defn, add.defn, smul.defn, real.sqrt_mono],
# )

norm_pos = kd.prove(  #
    kd.smt.ForAll([u], norm(u) >= 0), by=[norm2_pos, real.sqrt_pos, norm.defn]
)
norm2_zero = kd.prove(  # type: ignore
    kd.smt.ForAll([u], (norm2(u) == 0) == (u == vzero)),
    by=[norm2.defn, dot.defn],
)

dist = kd.define("dist", [u, v], real.sqrt(norm2(u - v)))
perp = kd.define("perp", [u, v], dot(u, v) == 0)

cross = kd.define(
    "cross",
    [u, v],
    Vec3(u.y * v.z - u.z * v.y, u.z * v.x - u.x * v.z, u.x * v.y - u.y * v.x),
)

cross_antisym = kd.prove(
    kd.smt.ForAll([u, v], cross(u, v) == -cross(v, u)),
    by=[neg.defn, cross.defn],
)
cross_add = kd.prove(
    kd.smt.ForAll([u, v, w], cross(u, v + w) == cross(u, v) + cross(u, w)),
    by=[cross.defn, add.defn],
)

cross_cross = kd.prove(
    kd.smt.ForAll(
        [u, v, w], cross(u, cross(v, w)) == smul(dot(u, w), v) - smul(dot(u, v), w)
    ),
    by=[cross.defn, dot.defn, sub.defn, smul.defn],
)
dot_cross = kd.prove(
    kd.smt.ForAll([u, v, w], dot(u, cross(v, w)) == dot(v, cross(w, u))),
    by=[cross.defn, dot.defn],
)

perp_cross = kd.prove(
    kd.smt.ForAll([u, v], perp(u, cross(u, v))),
    by=[cross.defn, perp.defn, dot.defn],
)

jacobi = kd.prove(
    kd.smt.ForAll(
        [u, v, w],
        cross(u, cross(v, w)) + cross(v, cross(w, u)) + cross(w, cross(u, v)) == vzero,
    ),
    by=[cross.defn, add.defn, sub.defn],
)
lagrange = kd.prove(
    kd.smt.ForAll(
        [u, v, w],
        dot(cross(u, v), cross(u, w)) == dot(u, u) * dot(v, w) - dot(u, v) * dot(u, w),
    ),
    by=[cross.defn, dot.defn],
)


@kd.Theorem(kd.smt.ForAll([u, v], dot(u, v) ** 2 <= norm2(u) * norm2(v)))
def cauchy_schwarz2(l):
    u, v = l.fixes()
    l.unfold(norm2)
    l.have(
        dot(cross(u, v), cross(u, v)) == dot(u, u) * dot(v, v) - dot(u, v) * dot(u, v),
        by=[lagrange(u, v, v)],
    )
    l.have(
        dot(cross(u, v), cross(u, v)) >= 0,
        by=[dot_self_pos(cross(u, v))],
    )
    l.auto()


@kd.Theorem(kd.smt.ForAll([u, v], real.abs(dot(u, v)) <= norm(u) * norm(v)))
def cauchy_schwarz(l):
    u, v = l.fixes()
    l.unfold(norm)
    l.have(dot(u, v) * dot(u, v) <= norm2(u) * norm2(v), by=[cauchy_schwarz2(u, v)])
    l.have(
        real.abs(dot(u, v)) == real.sqrt(real.sqr(dot(u, v))),
        by=[real.sqrt_sqr_abs(dot(u, v))],
    )
    l.rw(-1)
    l.clear(-1)
    l.unfold(real.sqr)
    l.unfold(norm2)
    l.rw(real.sqrt_mul, rev=True)
    l.auto(by=[dot_self_pos(u), dot_self_pos(v)])
    l.apply(real.sqrt_mono)
    l.split()
    l.auto(by=[dot_self_pos])
    l.auto(by=[dot_self_pos])
    l.auto(by=[norm2.defn])


# cauchy__schwarz = kd.prove(
#    smt.ForAll([u, v], real.abs(dot(u, v)) <= norm(u) * norm(v)),
#    by=[cauchy_schwarz2, real.sqrt_mul, real.sqrt_mono],
# )

"""
@kd.PTheorem(kd.smt.ForAll([u, v], norm(u + v) <= norm(u) + norm(v)))
def triangle(l):
    u, v = l.fixes()
    l.unfold(norm)
    l.unfold(dot)
    l.rw(norm2_add)
    l.
"""

"""
Vec3 = Vec(3)  # kd.Struct("Vec3", ("x", kd.R), ("y", kd.R), ("z", kd.R))
u, v = kd.smt.Consts("u v", Vec3)
# kd.notation.add.define([u, v], Vec3(u.x0 + v.x0, u.x1 + v.x1, u.x2 + v.x2))
# kd.notation.sub.define([u, v], Vec3(u.x0 - v.x0, u.x1 - v.x1, u.x2 - v.x2))
# norm2.define([u], u.x0 * u.x0 + u.x1 * u.x1 + u.x2 * u.x2)

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
"""
