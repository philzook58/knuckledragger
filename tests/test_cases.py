import pytest

import kdrag as kd
import kdrag.smt as smt


def test_multiple_cases_prove_original_goal_in_argument_order():
    n = smt.Int("n")
    l = kd.Lemma(smt.ForAll([n], smt.Abs(n) >= 0))
    x = l.fix()
    conditions = (x < 0, x == 0, x > 0)
    l.cases(*conditions)
    for condition in conditions:
        assert l.ctx[-1].eq(condition)
        l.auto()
    proof = l.qed()
    assert proof.thm.eq(smt.ForAll([n], smt.Abs(n) >= 0))


def test_multiple_cases_use_context_and_allow_overlap():
    n = smt.Int("n")
    goal = smt.Implies(n >= 0, n + 1 > 0)
    l = kd.Lemma(goal)
    l.intro()
    l.cases(n <= 1, n >= 1)
    l.auto()
    l.auto()
    assert l.qed().thm.eq(goal)


def test_coverage_must_hold_in_context():
    n = smt.Int("n")
    l = kd.Lemma(smt.Implies(n >= 0, n >= 0))
    l.intro()
    l.cases(n == 0, n > 0)
    l.auto()
    l.auto()
    l.qed()


def test_failed_coverage_leaves_state_unchanged():
    n = smt.Int("n")
    l = kd.Lemma(smt.BoolVal(True))
    goals = list(l.goals)
    lemmas = [dict(scope) for scope in l.lemmas]
    with pytest.raises(kd.kernel.SolverFailure):
        l.cases(n < 0, n > 0)
    assert all(a is b for a, b in zip(l.goals, goals))
    assert len(l.goals) == len(goals)
    assert l.lemmas == lemmas
    l.auto()
    l.qed()


def test_invalid_multiple_cases_leave_state_unchanged():
    n = smt.Int("n")
    l = kd.Lemma(smt.BoolVal(True))
    goal = l.top_goal()
    with pytest.raises(TypeError, match="Boolean conditions"):
        l.cases(n == 0, n)
    assert l.top_goal() is goal


def test_coverage_timeout_leaves_state_unchanged(monkeypatch):
    p = smt.Bool("p")
    l = kd.Lemma(p)
    goals = list(l.goals)
    lemmas = [dict(scope) for scope in l.lemmas]

    def timeout(*args, **kwargs):
        assert kwargs["timeout"] == 17
        raise TimeoutError("coverage timed out")

    monkeypatch.setattr(kd, "prove", timeout)
    with pytest.raises(TimeoutError, match="coverage timed out"):
        l.cases(p, smt.Not(p), timeout=17)
    assert len(l.goals) == len(goals)
    assert all(a is b for a, b in zip(l.goals, goals))
    assert l.lemmas == lemmas


def test_single_bool_retains_both_branches():
    p = smt.Bool("p")
    l = kd.Lemma(smt.BoolVal(True))
    l.cases(p)
    assert l.ctx[-1].eq(p == smt.BoolVal(True))
    l.auto()
    assert l.ctx[-1].eq(p == smt.BoolVal(False))
    l.auto()
    l.qed()


def test_single_datatype_retains_constructor_branches():
    T = kd.Enum("CasesOptionsTest", "A B")
    x = smt.Const("x", T)
    l = kd.Lemma(smt.Or(x == T.A, x == T.B))
    l.cases(x)
    l.auto()
    l.auto()
    l.qed()
