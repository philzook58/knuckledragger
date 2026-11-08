from kdrag import FreshVars, Lemma, QExists, QForAll, define, prove
from kdrag.smt import Const, FreshConst, Implies, Lambda, RealSort, RealVal, Reals  # noqa: F401
import kdrag.theories.real as real
import kdrag.theories.set as set_

# https://www.philipzucker.com/knuckle_analysis1/

x, y, z, r = FreshVars("x y z r", RealSort())

RSet = set_.Set(RealSort())
S = Const("S", RSet)


def Ball(x, r):
    """
    Ball returns a set of points y such that |y - x| < r

    >>> x,r = Reals("x r")
    >>> Ball(x,r)
    Lambda(y!..., absR(y!... - x) < r)
    """
    y = FreshConst(RealSort(), prefix="y")
    return Lambda([y], real.abs(y - x) < r)


ball = define("ball", [x, r], Ball(x, r))

is_open = define(
    "is_open",
    [S],
    QForAll([x], S[x], QExists([r], r > RealVal(0), ball(x, r) <= S)),
)
is_open_full = prove(is_open(RSet.full), unfold=1)
is_open_empty = prove(is_open(RSet.empty), unfold=1)

l = Lemma(is_open(ball(0, 1)))
l.unfold()
_x = l.fix()
l.intros()
l.exists(1 - real.abs(_x))
l.auto(unfold=2)
is_open_unit_ball = l.qed()


dist = define("R.dist", [x, y], real.abs(x - y))
dist_refl = prove(QForAll([x], dist(x, x) == 0), unfold=2)
dist_pos = prove(Implies(x != y, dist(x, y) > 0), unfold=2).forall([x, y])
dist_pos2 = prove(dist(x, y) >= 0, unfold=2).forall([x, y])
dist_sym = prove(QForAll([x, y], dist(x, y) == dist(y, x)), unfold=2)
dist_tri = prove(dist(x, z) <= dist(x, y) + dist(y, z), unfold=2).forall([x, y, z])
