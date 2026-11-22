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
    assert "  ✓ " in report


def test_ptheorem_prints_suggestions_when_enabled(capsys):
    x, y = smt.Reals("x y")
    kd.config.suggest = "lemmas"
    try:

        @kd.PTheorem(smt.ForAll([x, y], real.abs(x + y) <= real.abs(x) + real.abs(y)))
        def _tri(l):
            l.fixes()

    finally:
        kd.config.suggest = "off"
    assert "Suggestions" in capsys.readouterr().out
