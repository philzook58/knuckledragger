import pytest

import kdrag as kd
import kdrag.smt as smt


@pytest.mark.parametrize("forall", [smt.ForAll, kd.QForAll])
def test_implicit_premises_are_curried(forall):
    x = smt.Int("curried_x")
    expected = smt.RawForAll(x, smt.Implies(x >= 0, smt.Implies(x <= 0, x == 0)))
    assert forall([x], x >= 0, x <= 0, x == 0).eq(expected)
    grouped = smt.RawForAll(x, smt.Implies(smt.And(x >= 0, x <= 0), x == 0))
    assert forall([x], smt.And(x >= 0, x <= 0), x == 0).eq(grouped)


@pytest.mark.parametrize("forall", [smt.ForAll, kd.QForAll])
def test_curried_proof_application_and_intros(forall):
    x = smt.Int("curried_application_x")
    thm = forall([x], x >= 0, x <= 0, x == 0)
    pf = kd.prove(thm)
    zero = smt.IntVal(0)
    assert pf(zero)(kd.prove(zero >= 0), kd.prove(zero <= 0)).thm.eq(zero == 0)
    l = kd.Lemma(thm)
    x = l.fix()
    assert l.intros().eq(x >= 0)
    assert l.intros().eq(x <= 0)
    l.auto()
    l.qed()


@pytest.mark.parametrize("forall", [smt.ForAll, kd.QForAll])
def test_variable_assumptions_precede_explicit_premises(forall):
    x, y = smt.Ints("curried_assume_x curried_assume_y")
    x.assumes, y.assumes = x >= 0, y >= 0
    expected = smt.RawForAll(
        [x, y],
        smt.Implies(x >= 0, smt.Implies(y >= 0, smt.Implies(x <= y, x + y >= 0))),
    )
    assert forall([x, y], x <= y, x + y >= 0).eq(expected)


def test_well_formedness_is_a_separate_premise():
    from kdrag.theories.int import NatI

    x = smt.Const("curried_wf_x", NatI)
    x.assumes = x != NatI.mk(0)
    premise, conclusion = x == NatI.mk(1), x == NatI.mk(2)
    expected = smt.RawForAll(
        [x],
        smt.Implies(x.assumes, smt.Implies(x.wf(), smt.Implies(premise, conclusion))),
    )
    assert kd.QForAll([x], premise, conclusion).eq(expected)


@pytest.mark.parametrize("exists", [smt.Exists, kd.QExists])
def test_existential_premises_still_conjoin(exists):
    x = smt.Int("curried_exists_x")
    expected = smt.RawExists([x], smt.And(x >= 0, x <= 0))
    assert exists([x], x >= 0, x <= 0).eq(expected)


def test_curried_conditional_rewrite_keeps_all_obligations():
    x = smt.Int("curried_rewrite_x")
    rule = kd.prove(smt.ForAll([x], x >= 0, x <= 0, x + 2 == 2))
    l = kd.Lemma(smt.ForAll([x], x >= 0, x <= 0, x + 2 == 2))
    x = l.fix()
    l.intros()
    l.intros()
    l.rw(rule)
    assert l.goal.eq(smt.And(x >= 0, x <= 0))
    l.auto()
    l.auto()
    l.qed()


def test_apply_matches_an_implication_suffix():
    x = smt.Int("curried_apply_x")
    rule = kd.prove(smt.ForAll([x], x > 0, x < 0, smt.BoolVal(False)))
    l = kd.Lemma(smt.ForAll([x], x > 0, x < 0, smt.BoolVal(False)))
    x = l.fix()
    positive = l.intros()
    l.apply(rule)
    assert l.goal.eq(positive)
    l.assumption()
    l.qed()
