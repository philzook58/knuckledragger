from kdrag import smt
from kdrag.printers.pretty import pretty_expr, pretty_goal
from kdrag.tactics import Goal


def test_precedence_and_width():
    a, b, c = smt.Ints("a b c")
    p, q, r = smt.Bools("p q r")
    assert pretty_expr(a - (b - c)) == "a - (b - c)"
    assert pretty_expr(smt.Implies(smt.Implies(p, q), r)) == "(p → q) → r"
    assert pretty_expr(smt.Implies(p, smt.Implies(q, r))) == "p → q → r"
    f = smt.Function("long_call", smt.IntSort(), smt.IntSort(), smt.IntSort())
    assert pretty_expr(f(a, b)) == "long_call(a, b)"
    assert pretty_expr(f(a, b), width=12) == "long_call(a,\n  b)"


def test_goal_names_and_binders():
    eps, epsilon, x, xsub = smt.Ints("eps!4 ε₄ x!2 x₂")
    target = smt.RawForAll(
        [smt.Real("x₂")],
        smt.Exists([smt.Real("x₂")], x > xsub),
    )
    goal = Goal([eps, epsilon, x, xsub], [eps < epsilon], target)
    assert pretty_goal(goal) == (
        "eps!4 ε₄ x!2 x₂ : ℤ\n0: eps!4 < ε₄\n⊢ ∀x₂′1 : ℝ, ∃x₂′2 : ℝ, x!2 > x₂"
    )
    assert pretty_expr(eps > 0) == "ε₄ > 0"
    a, b = smt.Reals("alpha beta")
    assert pretty_expr(smt.RawForAll([a, b], a < b)) == "∀α β : ℝ, α < β"
    nested = smt.RawForAll([a], smt.Exists([b], a < b))
    assert pretty_expr(nested) == "∀α : ℝ, ∃β : ℝ, α < β"


def test_datatype_cases():
    color = smt.Datatype("Color")
    color.declare("red")
    color.declare("blue")
    color = color.create()
    x = smt.Const("x", color)
    term = smt.If(color.is_red(x), 1, smt.If(color.is_blue(x), 2, 0))
    assert pretty_expr(term, width=25).splitlines() == [
        "if is[red](x) then 1",
        "else if is[blue](x) then 2",
        "else 0",
    ]
