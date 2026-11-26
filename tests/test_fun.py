import pytest

import kdrag as kd
from kdrag import Fun, prove
from kdrag.smt import ForAll, Implies, Ints

x, y = Ints("x y")


def test_fun_names_binders_and_passes_goal_last():
    seen = []

    def body(a, b, goal):
        seen.extend([a, b, goal])
        return prove(goal)

    pf = Fun(ForAll([x, y], y > 0, x + y > x), body)
    a, b, goal = seen
    assert str(a).startswith("a!") and str(b).startswith("b!")
    assert goal.eq(Implies(b > 0, a + b > a))
    assert pf.thm.eq(ForAll([x, y], Implies(y > 0, x + y > x)))


def test_fun_opens_consecutive_quantifiers():
    thm = ForAll([x], ForAll([y], x + y == y + x))
    assert Fun(thm, lambda a, b, goal: prove(goal)).thm.eq(thm)


def test_fun_instantiates_lemmas_at_the_binders():
    sq1 = kd.define("test_fun_sq1", [x], x * x + 1)
    sq1_pos = prove(ForAll([x], sq1(x) > 0), by=[sq1.defn])
    thm = ForAll([x, y], sq1(x) + sq1(y) > 0)
    pf = Fun(thm, lambda a, b, goal: prove(goal, by=[sq1_pos(a), sq1_pos(b)]))
    assert pf.thm.eq(thm)


def test_fun_name_count_errors():
    thm = ForAll([x, y], x + y == y + x)
    with pytest.raises(ValueError, match="Need 2 names"):
        Fun(thm, lambda a, goal: prove(goal))
    with pytest.raises(ValueError, match="No ∀ left"):
        Fun(thm, lambda a, b, c, goal: prove(goal))


def test_fun_rejects_star_args_and_defaults():
    thm = ForAll([x], x == x)
    with pytest.raises(ValueError, match="plain positional"):
        Fun(thm, lambda *args: prove(args[-1]))
    with pytest.raises(ValueError, match="plain positional"):
        Fun(thm, lambda a, goal=None: prove(goal))


def test_fun_rejects_a_proof_of_the_wrong_goal():
    with pytest.raises(ValueError, match="proof of its goal"):
        Fun(ForAll([x], x == x), lambda a, goal: prove(a + 0 == a))
