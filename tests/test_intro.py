import pytest

from kdrag import Lemma, prove
from kdrag.smt import And, Bool, Bools, ForAll, Implies, Int, Not, Or, is_false


def test_intro_is_one_step_and_returns_one_premise():
    p, q = Bools("p q")
    pf = Lemma(Implies(p, Implies(q, p)))
    assert pf.intro().eq(p)
    assert pf.goal.eq(Implies(q, p))
    assert pf.intro().eq(q)
    pf.auto()
    pf.qed()


def test_intros_returns_the_chain_in_order_without_splitting_conjunctions():
    p, q, r = Bools("p q r")
    pf = Lemma(Implies(And(p, q), Implies(r, p)))
    grouped, extra = pf.intros()
    assert grouped.eq(And(p, q))
    assert extra.eq(r)
    assert pf.goal.eq(p)
    pf.auto()
    pf.qed()


def test_intros_stops_before_forall():
    p = Bool("p")
    n = Int("n")
    pf = Lemma(Implies(p, ForAll([n], Implies(n >= 0, n + 1 > 0))))
    assert pf.intros()[0].eq(p)
    assert pf.goal.is_forall()
    before = pf.top_goal()
    assert pf.intros() == []
    assert pf.top_goal() is before
    n = pf.fix()
    assert pf.intros()[0].eq(n >= 0)
    pf.auto()
    pf.qed()


@pytest.mark.parametrize(
    "goal",
    [
        Bool("atomic"),
        Not(Bool("negative")),
        Or(Not(Bool("p")), Bool("q")),
        Int("a") != Int("b"),
    ],
)
def test_intros_is_noop_without_an_explicit_implication(goal):
    pf = Lemma(goal)
    before = pf.top_goal()
    assert pf.intros() == []
    assert pf.top_goal() is before


def test_intro_preserves_negation_and_disequality_introduction():
    p = Bool("p")
    pf = Lemma(Not(p))
    assert pf.intro().eq(p)
    assert is_false(pf.goal)
    a, b = Int("a"), Int("b")
    pf = Lemma(a != b)
    assert pf.intro().eq(a == b)
    assert is_false(pf.goal)


def test_intro_errors_without_mutating_an_atomic_goal():
    pf = Lemma(Bool("atomic"))
    before = pf.top_goal()
    with pytest.raises(ValueError, match="Intro failed"):
        pf.intro()
    assert pf.top_goal() is before


def test_proof_call_reports_list_type_for_quantified_arguments():
    p, q = Bools("proof_list_p proof_list_q")
    rule = prove(ForAll(q, Implies(q, q)))
    l = Lemma(Implies(p, p))
    lems = l.intros()
    with pytest.raises(TypeError, match="expected ExprRef or Proof, got list") as exc:
        rule(lems)
    message = str(exc.value)
    assert "Proof argument 1" in message
    assert "intros" not in message
    assert rule(*lems).thm.eq(Implies(p, p))
    l.auto()
    l.qed()


def test_proof_call_reports_list_type_for_implication():
    p = Bool("proof_list_premise")
    rule = prove(Implies(p, p))
    l = Lemma(Implies(p, p))
    lems = l.intros()
    with pytest.raises(TypeError, match="expected ExprRef or Proof, got list"):
        rule(lems)
    l.specialize(rule, *lems)
    l.auto()
    l.qed()
