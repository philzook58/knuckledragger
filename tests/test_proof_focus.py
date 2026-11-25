import pytest

import kdrag as kd
from kdrag.smt import And, BoolVal, Int


def test_focus_exports_only_the_completed_claim():
    x = Int("x")
    l = kd.Lemma(x >= 0, assumes=[x > 0])
    claim = l.have(x >= 1)
    with l:
        assert not l.lemmas[-1]
        intermediate = l.have(x > -1, by=[])
        l.auto()
    assert len(l.lemmas[-1]) == 1
    assert l.ctx[-1].eq(claim)
    assert not any(h.eq(intermediate) for h in l.ctx)
    l.auto()
    l.qed()


def test_unfinished_focus_restores_goal_and_siblings():
    l = kd.Lemma(And(BoolVal(True), BoolVal(True)))
    l.split()
    original = l.top_goal()
    original_goals = l.goals.copy()
    with pytest.raises(ValueError, match="Unfinished focused proof"):
        with l:
            l.have(BoolVal(True), by=[])
    assert l.top_goal() is original
    assert all(a is b for a, b in zip(l.goals, original_goals, strict=True))
    assert not l.lemmas[-1]
    with l:
        l.auto()
    with l:
        l.auto()
    l.qed()


def test_exception_after_closing_focus_leaves_parent_goal_open():
    l = kd.Lemma(BoolVal(True))
    original = l.top_goal()
    with pytest.raises(RuntimeError, match="stop"):
        with l:
            l.auto()
            raise RuntimeError("stop")
    assert l.top_goal() is original
    assert not l.lemmas[-1]


def test_nested_focus_inside_explicit_subproof():
    x = Int("x")
    l = kd.Lemma(x - x == 0)
    with l.sub() as child:
        child.cases(x < 0)
        with child:
            child.auto()
        with child:
            child.auto()
    assert not l.goals
    assert l.qed().thm.eq(x - x == 0)
