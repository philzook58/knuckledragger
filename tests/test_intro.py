import kdrag as kd
import kdrag.smt as smt


def test_intro_is_one_step_and_intros_returns_a_list():
    p, q = smt.Bools("p q")
    l = kd.Lemma(smt.Implies(p, smt.Implies(q, p)))
    assert l.intro().eq(p)
    assert l.goal.eq(smt.Implies(q, p))
    remaining = l.intros()
    assert len(remaining) == 1
    assert remaining[0].eq(q)
    l.assumption()
    l.qed()


def test_intros_opens_the_curried_premise_chain():
    x = smt.Int("x")
    l = kd.Lemma(smt.ForAll(x, x >= 0, x <= 0, x == 0))
    x = l.fix()
    positive, negative = l.intros()
    assert positive.eq(x >= 0)
    assert negative.eq(x <= 0)
    assert l.goal.eq(x == 0)
    l.auto()
    l.qed()


def test_intros_keeps_an_explicit_conjunction_grouped():
    p, q, r = smt.Bools("p q r")
    l = kd.Lemma(smt.Implies(smt.And(p, q), smt.Implies(r, p)))
    grouped, extra = l.intros()
    assert grouped.eq(smt.And(p, q))
    assert extra.eq(r)
    l.auto()
    l.qed()


def test_intros_stops_at_quantifiers_and_non_implications():
    p = smt.Bool("p")
    x = smt.Int("x")
    l = kd.Lemma(smt.Implies(p, smt.ForAll(x, x >= 0, x + 1 > 0)))
    (premise,) = l.intros()
    assert premise.eq(p)
    assert l.goal.is_forall()
    before = l.top_goal()
    assert l.intros() == []
    assert l.top_goal() == before
    x = l.fix()
    (positive,) = l.intros()
    assert positive.eq(x >= 0)
    assert l.intros() == []
    l.auto()
    l.qed()
