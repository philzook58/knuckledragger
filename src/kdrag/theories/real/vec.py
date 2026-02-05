import kdrag as kd
import kdrag.smt as smt

import functools
import kdrag.theories.algebra.vector as vector
import operator

"""
Linear Algebra.

There are a number of modeling choices for N-dimensional vectors.
- Custom N field records
- Functions from FinSort(n) to RealSort
- Int -> Real subsets | forall i, i > N, v[i] = 0
- SeqSort(RealSort) | Length(v) == N

They all are the same but have greater or less difficulty.

"""

norm2 = vector.norm2
dot = vector.dot


@functools.cache
def FinSort(N):
    """
    Make a finite enumeration.

    >>> FinSort(3)
    Fin3
    """
    return kd.Enum("Fin" + str(N), " ".join(["X" + str(i) for i in range(N)]))


@functools.cache
def Fin0Sort(N):
    """
    A different style of finsort

    >>> Fin0Sort(3)
    Option_Option_Unit

    """
    # https://rocq-prover.org/doc/v9.0/stdlib/Stdlib.Vectors.Fin.html
    if N == 1:
        return kd.UnitSort()
    else:
        return kd.OptionSort(Fin0Sort(N - 1))
        # dt = kd.Inductive("Fin0_" + str(N))
        # dt.declare("Done")
        # dt.declare("Succ", Fin0Sort(N - 1))


@functools.cache
def SeqVec(N: smt.ExprRef | int):
    l = smt.Const("l", smt.SeqSort(smt.RealSort()))
    if isinstance(N, smt.ExprRef):
        assert kd.utils.free_in([l], N)
    return smt.Lambda([l], smt.Length(l) == N)


def FunVec(N: smt.ExprRef | int):
    v = smt.Array("v", smt.IntSort(), smt.RealSort())
    i = smt.Int("i")
    return smt.Lambda([v], smt.ForAll([i], smt.Or(i < 0, i >= N), v[i] == 0))


@functools.cache
def Vec0(N: int) -> smt.DatatypeSortRef:
    """

    >>> Vec2 = Vec0(2)
    >>> u, v = smt.Consts("u v", Vec2)
    >>> u[1]
    val(u)[X1]
    >>> dot(u, v)
    Vec0_2.dot(u, v)
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
    V = kd.Struct("Vec1_" + str(N), *[("x" + str(i), kd.R) for i in range(N)])
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


# R itself is a vector space

# banach fixed point https://en.wikipedia.org/wiki/Banach_fixed-point_theorem


V = smt.DeclareSort("Vec")
u, v, w = smt.Consts("u v w", V)
a, b = smt.Reals("a b")
smul = smt.Function("smul", smt.RealSort(), V, V)
add = smt.Function("add", V, V, V)
kd.notation.add.register(V, lambda x, y: add(x, y))

add_comm = kd.axiom(smt.ForAll([u, v], u + v == v + u))
add_assoc = kd.axiom(smt.ForAll([u, v, w], (u + v) + w == u + (v + w)))
zero = smt.Const("zero", V)
add_zero = kd.axiom(smt.ForAll([u], u + zero == u))
smul_assoc = kd.axiom(
    smt.ForAll([a, b, u], smul(a, smul(b, u)) == smul(a * b, u))
)  # trigger left to right?
smul_add = kd.axiom(smt.ForAll([a, b, u], smul(a + b, u) == smul(a, u) + smul(b, u)))
smul_vadd = kd.axiom(smt.ForAll([a, u, v], smul(a, u + v) == smul(a, u) + smul(a, v)))

# zero_unique
# smul_one
# smul_zero
#


# VSet = smt.ArraySort(V, smt.BoolSort())
# closed = kd.define("closed", [S], smt.ForAll([u, v, a, b], S[u], S[v], S[smul(a, u) + smul(b, v)])) # is_linear ?
# is_basis = kd.define("is_basis", [S], smt.ForAll([u], S[u], smt.Exists([a1, a2, a3], u == smul(a1, ihat) + smul(a2, jhat) + smul(a3, khat))))
# span = kd.define("span", [S], smt.Lambda([v], ))

# f = smt.Array("f", V, V)
# is_linear = kd.define("is_linear", [f], smt.ForAll([u, v, a, b], f[smul(a, u) + smul(b, v)] == smul(a, f[u]) + smul(b, f[v])))
