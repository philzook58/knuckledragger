import pytest

from kdrag import Theorem
from kdrag.smt import ForAll, Implies, Int, Ints
import kdrag.theories.nat as nat

x, y = Ints("x y")


def test_theorem_names_binders_and_hypotheses():
    seen = []

    @Theorem(ForAll([x, y], x > 0, y > 0, x + y > 1))
    def pos_add(l, a, b, ha, hb):
        seen.extend([a, b, ha, hb])
        l.auto()

    a, b, ha, hb = seen
    assert str(a).startswith("a!") and str(b).startswith("b!")
    assert ha.eq(a > 0) and hb.eq(b > 0)


def test_theorem_opens_parameters_and_stops():
    @Theorem(ForAll([x], x >= 0, ForAll([y], y >= 0, x + y >= 0)))
    def stops(l, a, ha):
        # The inner ForAll is still in the goal.
        assert l.goal.is_forall()
        l.auto()

    assert stops.thm.eq(
        ForAll([x], Implies(x >= 0, ForAll([y], Implies(y >= 0, x + y >= 0))))
    )


def test_theorem_needs_a_name_per_binder():
    with pytest.raises(ValueError, match="Need 2 names"):

        @Theorem(ForAll([x, y], x + y == y + x))
        def _(l, a):
            pass


def test_theorem_rejects_defaults_and_star_args():
    with pytest.raises(ValueError, match="plain positional"):

        @Theorem(ForAll([x], x == x))
        def _(l, a=0):
            pass

    with pytest.raises(ValueError, match="plain positional"):

        @Theorem(ForAll([x], x == x))
        def _(l, *rest):
            pass


def test_theorem_parameters_before_induction():
    n, m = nat.x, nat.y

    @Theorem(ForAll([n, m], nat.add(n, m) == nat.add(m, n)))
    def add_comm(l, n, m):
        l.induct(n)
        l.auto(by=[nat.add.defn, nat.add_Z_r])
        l.fix()
        l.auto(by=[nat.add.defn, nat.add_s_r])

    assert add_comm.thm.eq(nat.add_comm.thm)


def test_theorem_without_parameters_is_unchanged():
    a = Int("a")

    @Theorem(a + 1 > a)
    def plain(l):
        l.auto()

    assert plain.thm.eq(a + 1 > a)
