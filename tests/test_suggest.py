import kdrag as kd
import kdrag.smt as smt
import kdrag.suggest as suggest
import kdrag.theories.real as real


def test_rank_finds_matching_library_lemma():
    x, y = smt.Reals("x y")
    goal = real.abs(x + y) <= real.abs(x) + real.abs(y)
    assert "kdrag.theories.real.abs_add" in [s.name for s in suggest.rank(goal)]


def test_report_marks_lemma_that_closes_goal():
    x, y = smt.Reals("x y")
    report = suggest.report(real.abs(x + y) <= real.abs(x) + real.abs(y))
    assert "  ✅ " in report


def test_suggest_prints_goal_first(capsys):
    x, y = smt.Reals("x y")
    l = kd.Lemma(smt.ForAll([x, y], real.abs(x + y) <= real.abs(x) + real.abs(y)))
    l.fixes()
    l.suggest()
    out = capsys.readouterr().out
    assert out.index("⊢") < out.index("Suggestions")


n = smt.Int("n")
# Module level, as definitions are; the z3 name differs on purpose.
my_succ = kd.define("sugg_test_succ", [n], n + 1)


def test_definitions_named_by_python_variable():
    names = [s.name for s in suggest.rank(my_succ(n) > n)]
    assert "my_succ.defn" in names
    assert "sugg_test_succ.defn" not in names
