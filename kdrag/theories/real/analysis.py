import kdrag as kd
import kdrag.smt as smt
import kdrag.theories.real as real
import kdrag.theories.set as set_

# https://www.philipzucker.com/knuckle_analysis1/

x, y, z, r = kd.FreshVars("x y z r", smt.RealSort())

RSet = set_.Set(smt.RealSort())
S = smt.Const("S", RSet)


def Ball(x, r):
    """
    Ball returns a set of points y such that |y - x| < r

    >>> x,r = smt.Reals("x r")
    >>> Ball(x,r)
    Lambda(y!..., absR(y!... - x) < r)
    """
    y = smt.FreshConst(smt.RealSort(), prefix="y")
    return smt.Lambda([y], real.abs(y - x) < r)


ball = kd.define("ball", [x, r], Ball(x, r))

is_open = kd.define(
    "is_open",
    [S],
    kd.QForAll([x], S[x], kd.QExists([r], r > smt.RealVal(0), ball(x, r) <= S)),
)
is_open_full = kd.prove(is_open(RSet.full), unfold=1)
is_open_empty = kd.prove(is_open(RSet.empty), unfold=1)

l = kd.Lemma(is_open(ball(0, 1)))
l.unfold()
_x = l.fix()
l.intros()
l.exists(1 - real.abs(_x))
l.auto(unfold=2)
is_open_unit_ball = l.qed()


dist = kd.define("dist", [x, y], real.abs(x - y))  # type: ignore
dist_refl = kd.prove(kd.QForAll([x], dist(x, x) == 0), unfold=2)
dist_pos = kd.prove(smt.Implies(x != y, dist(x, y) > 0), unfold=2).forall([x, y])
dist_pos2 = kd.prove(dist(x, y) >= 0, unfold=2).forall([x, y])
dist_sym = kd.prove(kd.QForAll([x, y], dist(x, y) == dist(y, x)), unfold=2)
dist_tri = kd.prove(dist(x, z) <= dist(x, y) + dist(y, z), unfold=2).forall([x, y, z])
