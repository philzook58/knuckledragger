import kdrag as kd
import kdrag.smt as smt
from kdrag.rewrite import backward_rule, forward_rule, rule_of_expr


def test_rule_preserves_premise_order_and_grouping():
    a, b, c, d = smt.Bools("a b c d")
    grouped = smt.And(a, b)
    implication = smt.Implies(b, c)
    thm = smt.Implies(grouped, smt.Implies(implication, d))
    rule = rule_of_expr(thm)
    assert len(rule.hyps) == 2
    assert rule.hyps[0].eq(grouped)
    assert rule.hyps[1].eq(implication)
    assert rule.conc.eq(d)
    assert rule.to_expr().eq(thm)


def test_fact_has_no_premises():
    a = smt.Bool("a")
    rule = rule_of_expr(a)
    assert rule.hyps == []
    assert rule.to_expr().eq(a)
    subst, obligation = backward_rule(rule, a)
    assert subst == {}
    assert smt.is_true(obligation)


def test_quantified_rule_freshening_and_roundtrip():
    x = smt.Int("x")
    pf = kd.prove(smt.ForAll([x], x >= 0, x <= 0, x == 0))
    rule = rule_of_expr(pf)
    assert rule.to_expr().body().eq(pf.thm.body())
    fresh = rule.freshen()
    assert fresh.pf is pf
    assert not fresh.vs[0].eq(rule.vs[0])
    assert fresh.to_expr().body().eq(pf.thm.body())
    subst, obligation = backward_rule(fresh, smt.IntVal(0) == 0)
    assert subst[fresh.vs[0]].eq(smt.IntVal(0))
    assert obligation.eq(smt.And(smt.IntVal(0) >= 0, smt.IntVal(0) <= 0))


def test_backward_rule_matches_only_at_premise_boundaries():
    a, b, c = smt.Bools("a b c")
    target = smt.Implies(b, c)
    curried = rule_of_expr(smt.Implies(a, target))
    subst, obligation = backward_rule(curried, target)
    assert subst == {}
    assert obligation.eq(a)
    grouped = rule_of_expr(smt.Implies(smt.And(a, b), c))
    assert backward_rule(grouped, target) is None
    _, obligation = backward_rule(grouped, c)
    assert obligation.eq(smt.And(a, b))


def test_forward_rule_matches_combined_premises():
    a, b, c = smt.Bools("a b c")
    rule = rule_of_expr(smt.Implies(a, smt.Implies(b, c)))
    assert forward_rule(rule, smt.And(a, b)).eq(c)
    assert forward_rule(rule, a) is None
    assert forward_rule(rule_of_expr(c), smt.BoolVal(True)).eq(c)
