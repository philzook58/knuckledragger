import kdrag as kd
import kdrag.smt as smt
import kdrag.theories.real as R
import functools
import kdrag.theories.algebra.vector as vector
import operator

"""
Linear Algebra
"""

norm2 = vector.norm2
dot = vector.dot


Vec2 = kd.Struct("Vec2", ("x", kd.R), ("y", kd.R))
u, v = kd.smt.Consts("u v", Vec2)
add = kd.notation.add.define([u, v], Vec2(u.x + v.x, u.y + v.y))
sub = kd.notation.sub.define([u, v], Vec2(u.x - v.x, u.y - v.y))
kd.notation.neg.define([u], Vec2(-u.x, -u.y))


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


@functools.cache
def FinSort(N):
    """
    Make a finite enumeration.

    >>> FinSort(3)
    Fin3
    """
    return kd.Enum("Fin" + str(N), " ".join(["X" + str(i) for i in range(N)]))


@functools.cache
def Vec0(N: int) -> smt.DatatypeSortRef:
    """

    >>> Vec2 = Vec0(2)
    >>> u, v = smt.Consts("u v", Vec2)
    >>> u[1]
    val(u)[X1]
    >>> dot(u, v)
    dot(u, v)
    """
    Fin = FinSort(N)
    S = kd.NewType("Vec0_" + str(N), smt.ArraySort(Fin, kd.R))
    i, j, k = smt.Consts("i j k", FinSort(N))
    u, v, w = smt.Consts("u v w", S)
    a, b = smt.Reals("a b")

    def getitem(x, i):
        if isinstance(i, int):
            if i < 0 or i >= N:
                raise ValueError("Out of bounds", x, i)
            return x.val[Fin.constructor(i)()]
        else:
            return x.val[i]

    kd.notation.getitem.register(S, getitem)
    S.add = kd.notation.add.define([u, v], S(smt.Lambda([i], u[i] + v[i])))
    S.sub = kd.notation.sub.define([u, v], S(smt.Lambda([i], u[i] - v[i])))
    S.neg = kd.notation.neg.define([u], S(smt.Lambda([i], -u[i])))
    S.dot = dot.define(
        [u, v], functools.reduce(operator.add, (u[i] * v[i] for i in Fin))
    )
    S.add_comm = kd.prove(smt.ForAll([u, v], u + v == v + u), by=[S.add.defn])
    S.add_assoc = kd.prove(
        smt.ForAll([u, v, w], (u + v) + w == u + (v + w)), by=[S.add.defn]
    )
    S.zero = S(smt.K(Fin, smt.RealVal(0)))
    S.add_zero = kd.prove(smt.ForAll([u], u + S.zero == u), by=[S.add.defn])
    S.smul = kd.define("smul", [a, u], S(smt.Lambda([i], a * u[i])))
    smul = S.smul
    S.smul_one = kd.prove(smt.ForAll([u], smul(1, u) == u), by=[S.smul.defn])
    S.smul_zero = kd.prove(smt.ForAll([u], smul(0, u) == S.zero), by=[S.smul.defn])
    S.norm2 = norm2.define([u], sum(u[i] * u[i] for i in Fin))
    S.norm_pos = kd.prove(smt.ForAll([u], S.norm2(u) >= 0), by=[S.norm2.defn])

    return S


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
    V.zero = V(*[0 for i in range(N)])
    V.norm2 = norm2.define([u], sum(u[i] * u[i] for i in range(N)))
    V.dot = dot.define([u, v], sum(u[i] * v[i] for i in range(N)))
    return V


Vec3 = Vec(3)  # kd.Struct("Vec3", ("x", kd.R), ("y", kd.R), ("z", kd.R))
u, v = kd.smt.Consts("u v", Vec3)
# kd.notation.add.define([u, v], Vec3(u.x0 + v.x0, u.x1 + v.x1, u.x2 + v.x2))
# kd.notation.sub.define([u, v], Vec3(u.x0 - v.x0, u.x1 - v.x1, u.x2 - v.x2))
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


# R itself is a vector space

# banach fixed point https://en.wikipedia.org/wiki/Banach_fixed-point_theorem
