import pytest

import kdrag as kd
import kdrag.smt as smt


@pytest.mark.parametrize("keep", [False, True])
def test_specialize_context_premise(keep):
    x, y = smt.Ints("x y")
    rule = smt.ForAll(x, x > 0, x >= 0)
    l = kd.Lemma(smt.Implies(rule, smt.Implies(y > 0, y >= 0)))
    hyp = l.intros()
    positive = l.intros()
    result = l.specialize(hyp, y, positive, keep=keep)
    assert result.eq(y >= 0)
    assert any(h.eq(hyp) for h in l.ctx) == keep
    assert any(h.eq(positive) for h in l.ctx)
    l.assumption()
    l.qed()


def test_specialize_proof_premise_and_nested_quantifiers():
    x, y, z = smt.Ints("x y z")
    rule = kd.prove(
        smt.ForAll(
            x,
            smt.Implies(smt.BoolVal(True), smt.ForAll([y, z], x + y + z == z + y + x)),
        )
    )
    l = kd.Lemma(smt.IntVal(1) + 2 + 3 == smt.IntVal(3) + 2 + 1)
    truth = kd.prove(smt.BoolVal(True))
    result = l.specialize(rule, 1, truth, 2, 3)
    assert result.eq(l.goal)
    l.assumption()
    l.qed()


def test_specialize_multiple_implication_premises():
    p = smt.Bool("p")
    rule = smt.Implies(p, smt.Implies(smt.BoolVal(True), p))
    l = kd.Lemma(smt.Implies(rule, smt.Implies(p, p)))
    hyp, premise = l.intros(), l.intros()
    result = l.specialize(hyp, premise, kd.prove(smt.BoolVal(True)))
    assert result.eq(p)
    l.assumption()
    l.qed()


def test_specialize_boolean_term_is_not_premise_evidence():
    b, outside = smt.Bools("b outside")
    rule = kd.prove(smt.ForAll(b, smt.Or(b, smt.Not(b))))
    l = kd.Lemma(smt.Or(outside, smt.Not(outside)))
    result = l.specialize(rule, outside)
    assert result.eq(l.goal)
    l.assumption()
    l.qed()


def test_specialize_rejects_formula_not_in_context():
    x = smt.Int("x")
    rule = smt.ForAll(x, x > 0, x >= 0)
    l = kd.Lemma(smt.Implies(rule, smt.BoolVal(True)))
    hyp = l.intros()
    before = l.top_goal()
    # Even a true formula needs to be in the context to be premise evidence.
    with pytest.raises(KeyError, match="not found in context"):
        l.specialize(hyp, 1, smt.IntVal(1) > 0)
    assert l.top_goal() == before


def test_specialize_rejects_mismatched_premises():
    p, q, r = smt.Bools("p q r")
    rule = smt.Implies(p, q)
    l = kd.Lemma(smt.Implies(rule, smt.Implies(r, smt.BoolVal(True))))
    hyp, wrong = l.intros(), l.intros()
    before = l.top_goal()
    with pytest.raises(ValueError, match="does not match"):
        l.specialize(hyp, wrong)
    with pytest.raises(ValueError, match="does not match"):
        l.specialize(hyp, kd.prove(smt.BoolVal(True)))
    assert l.top_goal() == before


def test_specialize_checks_argument_kinds():
    x, y = smt.Ints("x y")
    rule = kd.prove(smt.ForAll([x, y], x + y == y + x))
    l = kd.Lemma(smt.BoolVal(True))
    with pytest.raises(ValueError, match="at least one argument"):
        l.specialize(rule)
    with pytest.raises(ValueError, match="each quantified variable"):
        l.specialize(rule, 1)
    with pytest.raises(TypeError, match="not Proofs"):
        l.specialize(rule, kd.prove(smt.BoolVal(True)), 1)
    implication = kd.prove(smt.Implies(smt.BoolVal(True), smt.BoolVal(True)))
    with pytest.raises(TypeError, match="Proofs or context formulas"):
        l.specialize(implication, 1)
    assert not l.ctx
