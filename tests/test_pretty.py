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
    eps, epsilon, x, xsub = smt.Ints("eps!4 ε₁ x!2 x₀")
    target = smt.RawForAll(
        [smt.Real("x₀")],
        smt.Exists([smt.Real("x₀")], x > xsub),
    )
    goal = Goal([eps, epsilon, x, xsub], [eps < epsilon], target)
    conclusion = "⊢ ∀x₀′1 : ℝ, ∃x₀′2 : ℝ, x!2 > x₀"
    assert pretty_goal(goal).splitlines() == [
        "eps!4 ε₁ x!2 x₀ : ℤ",
        "0: eps!4 < ε₁",
        "─" * len(conclusion),
        conclusion,
    ]
    assert pretty_goal(goal, width=12).splitlines()[2] == "─" * 12
    assert pretty_goal(Goal([], [], eps > 0)) == "⊢ ε₀ > 0"
    assert pretty_expr(eps > 0) == "ε₀ > 0"
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


def test_fresh_names_follow_numeric_order():
    later, earlier = smt.Ints("x!100 x!20")
    assert pretty_expr(later > earlier) == "x₁ > x₀"
    assert pretty_expr(later > 0) == "x₀ > 0"


def test_registered_notation():
    from kdrag.theories import nat
    from kdrag.theories.real import seq

    x, y = smt.Consts("x y", nat.Nat)
    assert pretty_expr(nat.add(x, y)) == "x + y"
    assert pretty_expr(nat.add(x, nat.add(y, x))) == "x + (y + x)"
    a, b = smt.Consts("a b", seq.RSeq)
    assert pretty_expr((a + b)[0]) == "(a + b)[0]"
