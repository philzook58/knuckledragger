import kdrag as kd
import kdrag.smt as smt
from kdrag.smt import Store, K, Exists, Reals, Lambda, And, Not, ForAll, If
from kdrag import Theorem, define, PTheorem, prove  # noqa: F401

import kdrag.theories.real as real
import kdrag.theories.real.vec2 as vec2
import kdrag.theories.set as set_

x, y, z = Reals("x y z")

Point2D = vec2.Vec2
p, q, a, b, c = smt.Consts("p q a b c", Point2D)

Shape = set_.Set(Point2D)
A, B, C = smt.Consts("A B C", Shape)

point = kd.define("point", [p], Store(K(Point2D, False), p, True))
is_point = kd.define("is_point", [A], Exists([p], point(p) == A))

"""
line = define(
    "line",
    [x, y, z],
    Lambda(
        [p],
        p.x * x + p.y * y + z == 0,
    ),
)
"""

line = define("line", [p, q], Lambda([a], vec2.cross(a - p, q - p) == 0))

is_line = define(
    "is_line",
    [A],
    Exists([p, q], p != q, ForAll([a], line(p, q)[a] == A[a])),
)

_is_line1 = prove(
    ForAll(
        [A],
        Exists([p, q], is_line(A) == And(p != q, ForAll([a], line(p, q)[a] == A[a]))),
    ),
    by=[is_line.defn],
)
(lp1, lp2), lp_defn = kd.kernel.choose(_is_line1)

is_perp = define("is_perp", [A, B], vec2.dot(lp1(A) - lp2(A), lp1(B) - lp2(B)) == 0)
is_parallel = define(
    "is_parallel", [A, B], vec2.cross(lp1(A) - lp2(A), lp1(B) - lp2(B)) == 0
)

midp = define("midp", [p, q], vec2.smul(0.5, p + q))

coll = define(
    "collinear",
    [p, q, a],
    vec2.cross(q - p, a - p) == 0,
)
coll_swap = prove(
    ForAll([p, q, a], coll(p, q, a) == coll(q, p, a)),
    by=[coll.defn, vec2.cross.defn, vec2.sub.defn],
)
coll_swap2 = prove(
    ForAll([p, q, a], coll(p, q, a) == coll(p, a, q)),
    by=[coll.defn, vec2.cross.defn, vec2.sub.defn],
)

bet = define(
    "between",
    [p, q, a],
    And(coll(p, q, a), vec2.dot(q - p, a - p) >= 0, vec2.dot(p - q, a - q) >= 0),
)

midp_coll = prove(
    ForAll([p, q, a], coll(p, midp(p, q), q)),
    by=[
        coll.defn,
        midp.defn,
        vec2.cross.defn,
        vec2.sub.defn,
        vec2.add.defn,
        vec2.smul.defn,
    ],
)

cong = define(
    "cong_seg",
    [p, q, a, b],
    vec2.norm2(p - q) == vec2.norm2(a - b),
)
cong_refl = prove(
    ForAll([p, q], cong(p, q, p, q)), by=[cong.defn, vec2.norm2.defn, vec2.sub.defn]
)
cong_symm = prove(
    ForAll([p, q, a, b], cong(p, q, a, b) == cong(a, b, p, q)),
    by=[cong.defn, vec2.sub.defn],
)

ray = define(
    "ray",
    [p, q],
    Lambda(
        [a],
        And(coll(p, q, a), vec2.dot(q - p, a - p) >= 0),
    ),
)

origin = Point2D(0, 0)
dir = define("dir", [p], ray(origin, p))
# A direction _is_ an angle.
is_dir = define(
    "is_dir", [A], Exists([p], p != origin, vec2.norm2(p) == 1, dir(p) == A)
)
_is_dir1 = prove(
    ForAll(
        [A],
        Exists([p], is_dir(A) == And(p != origin, vec2.norm2(p) == 1, dir(p) == A)),
    ),
    by=[is_dir.defn],
)
(unit,), unit_defn = kd.kernel.choose(_is_dir1)

# is_dir_dir = prove(ForAll([p], p != origin, is_dir(dir(p))), by=[is_dir.defn, dir.defn])


"""
@PTheorem(ForAll(p, p != origin, is_dir(dir(p))))
def unit_dir(l):
    p = l.fix()
    l.intros()
    l.unfold(is_dir)
    l.exists(vec2.smul(1 / vec2.norm(p), p))
    l.unfold(vec2.norm)

    l.have(vec2.norm2(p) != 0, by=[vec2.norm2_zero])
    l.have(vec2.norm2(p) > 0, by=[vec2.norm2_pos])
    l.have(real.sqrt(vec2.norm2(p)) != 0, by=[real.sqrt_define(vec2.norm2(p))])
    l.have(vec2.norm2(p) == vec2.dot(p, p), by=[vec2.norm2.defn])
    l.split()
    l.auto(by=[vec2.dot.defn, vec2.smul.defn])

    l.unfold(vec2.norm2, vec2.smul, vec2.dot)
    l.unfold(vec2.dot)
    l.simp()
    l.have(
        real.sqrt(p.x * p.x + p.y * p.y) ** 2 == p.x * p.x + p.y * p.y,
        by=[real.sqrt_square(p.x * p.x + p.y * p.y)],
    )
    l.auto()
    # l.have(is_dir(dir(p))

"""

"""
seg = define(
    "seg",
    [p, q],
    Lambda(
        [a],
        And(coll(p, q, a), vec2.dot(q - p, a - p) >= 0, vec2.dot(p - q, a - q) >= 0),
    ),
)

is_seg = define(
    "is_seg",
    [A],
    Exists([p, q], p != q, ForAll([a], seg(p, q)[a] == A[a])),
)
_is_seg1 = prove(
    ForAll(
        [A],
        Exists([p, q], is_seg(A) == And(p != q, ForAll([a], seg(p, q)[a] == A[a]))),
    ),
    by=[is_seg.defn],
)
(endp1, endp2), sp_defn = kd.kernel.choose(_is_seg1)
"""


"""
is_line(A) is_line(B) -> is_parallel -> exists point in intersection

https://geocoq.github.io/GeoCoq/

Angle is canonical line?
Just use dot product as angle?


is_line = kd.define(
    "is_line",
    [A],
    Exists([x, y, z], Not(And(x == 0, y == 0)), ForAll([p], line(x, y, z)[p] == A[p])),
)
@Theorem(
    ForAll(
        [A],
        Exists([p, q], Not(p == q), ForAll([a], linep(p, q)[a] == A[a])),
        is_line(A),
    )
)
def is_line_iff_linep(l):
    A = l.fix()
    l.unfold(is_line)
    l.unfold(linep)
    l.unfold(line)
    l.unfold(vec2.cross)
    l.unfold(vec2.sub)
    # l.split()
    # -> implication
    l.intros()
    p, q = l.obtain(0)
    l.exists(p.y - q.y, q.x - p.x, p.x * q.y - p.y * q.x)
    l.auto()
"""
"""
        # <- implication
        l.intros()
        x, y, z = l.obtain(0)
        l.cases(x == 0)

        l.case(x == 0)
        l.have(y != 0, by=[])
        l.exists(Point2D(0, -z / y), Point2D(1, -(z / y)))
        l.auto()

        l.case(x != 0)
        l.exists(Point2D(-(y + z) / x, 1), Point2D(-(z - y) / x, -1))
        l.split()
        l.auto()
        a = l.fix()
        l.simp()
        l.split(0)
        l.specialize(1, a)
        l.simp(1)

        l.rw(1, rev=True)
        l.clear(1)
        # l.model()
        # l.auto()
        l.have(x != 0, by=[])
        l.clear(0)
        l.clear(0)
        l.cases(smt.simplify(x * a.x + y * a.y + z == 0))
        l.rw(-1)
        l.abort()
        # l.auto()

        # l.auto()
        # l.auto()
        # l.model(x, y, z, a, p, q)

        # l.exists(
        #    If(x == 0, Point2D(0, -z / y), Point2D(-(y + z) / x, 1)),
        #    If(y == 0, Point2D(-z / x, 0), Point2D(1, -(x + z) / y)),
        # )
        # l.simp()
        # l.auto()
"""


# seg = define("seg", [p, q], Lambda([a], vec2.cross()))
# is_seg = define(
#    "is_seg",
#    [A],
# )


circle = kd.define(
    "circle", [c, p], smt.Lambda([q], vec2.norm2(p - c) == vec2.norm2(q - c))
)


is_circle = kd.define(
    "is_circle", [A], smt.Exists([c, q], ForAll(p, circle(c, q)[p] == A[p]))
)
# center, circp = kd.kernel.choose

# convex = kd.define("convex", [A], kd.QForAll([p, q], A(p), A(q), A(vec.Vec2(smul(0.5, p + q)))))
