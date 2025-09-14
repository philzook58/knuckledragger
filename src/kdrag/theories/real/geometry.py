import kdrag as kd
import kdrag.smt as smt

# import kdrag.theories.real as real
import kdrag.theories.real.vec as vec
import kdrag.theories.set as set_


Point2D = vec.Vec2
p, q, a, b, c = smt.Consts("p q a b c", Point2D)

r = smt.Real("r")
circle = kd.define("circle", [c, r], smt.Lambda([p], vec.norm2(p - c) == r * r))

Shape = set_.Set(Point2D)

A, B, C = smt.Consts("A B C", Shape)

is_circle = kd.define("is_circle", [A], smt.Exists([c, r], circle(c, r) == A))


# convex = kd.define("convex", [A], kd.QForAll([p, q], A(p), A(q), A(vec.Vec2(smul(0.5, p + q)))))
