import sys
from textwrap import dedent

from kdrag import smt
from kdrag.tactics import Goal
from tools.proof_trace import Step, Target, active_goal, record, render


def test_record_multiline_proof_with_split_and_instantiated_lemma(
    tmp_path, monkeypatch
):
    module_name = "proof_trace_fixture"
    (tmp_path / f"{module_name}.py").write_text(
        dedent(
            """\
            from kdrag import Theorem, prove, smt

            x, y = smt.Ints("trace_x trace_y")
            reflexive = prove(smt.ForAll([x], x <= x))

            @Theorem(smt.And(smt.BoolVal(True), y <= y))
            def example(l):
                # Solve the two conjuncts.
                l.split()
                l.auto()
                l.auto(
                    by=[reflexive(y)],
                )
            """
        ),
        encoding="utf-8",
    )
    monkeypatch.syspath_prepend(str(tmp_path))
    try:
        [(target, statement, steps)] = record(
            [Target(module_name, "example")], "unused-revision"
        )
    finally:
        sys.modules.pop(module_name, None)

    assert len(steps) == 3
    split, switch, finish = steps
    assert len(split.after) == 2
    assert "trace_y" not in active_goal(split.after, split.before)
    assert "trace_y" in active_goal(switch.after, switch.before)
    assert "+ " not in active_goal(switch.after, switch.before)
    assert finish.source == "l.auto(\n    by=[reflexive(y)],\n)"
    [reference] = finish.references
    y = smt.Int("trace_y")
    assert reference.statement.eq(y <= y)
    assert not finish.after

    markdown = render(target, statement, steps)
    assert "<p>Solve the two conjuncts.</p>" in markdown
    assert '<span title="trace_y ≤ trace_y">reflexive</span>(y)' in markdown
    assert "Goal 1" not in markdown
    assert "**Starting state**" not in markdown
    assert "No open goals." in markdown


def test_active_goal_highlights_additions_only():
    p, q, r = smt.Bools("p q r")
    before = (Goal([], [p, q], r),)
    removed = active_goal((Goal([], [q], r),), before)
    assert "0: q" in removed and "0: p" not in removed
    assert "\n+ " not in removed and "\n- " not in removed

    replaced = active_goal((Goal([], [smt.Not(p), q], r),), before)
    assert "+ 0: ¬p" in replaced
    assert "\n- " not in replaced


def test_render_keeps_starting_state_when_it_adds_context():
    p, q = smt.Bools("p q")
    step = Step(line=8, source="l.auto()", before=(Goal([], [p], q),))
    markdown = render(Target("theory", "example"), q, [step])
    assert "**Starting state**" in markdown
    assert "0: p" in markdown
