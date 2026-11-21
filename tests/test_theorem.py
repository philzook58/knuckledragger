import pytest

from kdrag import Proof, PTheorem, Theorem
from kdrag.smt import BoolVal, Implies, Int
from kdrag.tactics import _AutoFailure


offset = 1
globals_only = 3


@pytest.mark.parametrize("decorator", [Theorem, PTheorem])
def test_string_goal_uses_caller_scope(decorator, capsys):
    x = Int("theorem_local_x")
    offset = 2

    @decorator("x + offset > x")
    def local(l):
        assert l.goal.eq(x + offset > x)
        l.auto()

    @decorator("x + globals_only > x")
    def global_name(l):
        assert l.goal.eq(x + globals_only > x)
        l.auto()

    if decorator is Theorem:
        assert isinstance(local, Proof) and isinstance(global_name, Proof)
        assert capsys.readouterr().out == ""
    else:
        assert local is None and global_name is None
        assert capsys.readouterr().out.count("Lemma Complete!") == 2


def test_preview_displays_unfinished_goal(capsys):
    x = Int("unfinished_x")

    @PTheorem(Implies(x > 0, x >= 0))
    def unfinished(l):
        l.intro()

    assert unfinished is None
    output = capsys.readouterr().out
    assert "Next Goal:" in output
    assert "unfinished_x > 0" in output and "unfinished_x ≥ 0" in output


def test_theorem_preserves_metadata_and_positional_timing(capsys):
    @Theorem(BoolVal(True), True)
    def complete(l):
        """Proof metadata."""
        l.auto()

    assert isinstance(complete, Proof)
    assert complete.__doc__ == "Proof metadata."
    assert complete.__name__ == "complete"
    assert complete.__module__ == __name__
    assert "Starting theorem complete" in capsys.readouterr().out


def test_theorem_propagates_solver_failure(capsys):
    with pytest.raises(_AutoFailure):

        @Theorem(BoolVal(False))
        def impossible(l):
            l.auto()

    assert capsys.readouterr().out == ""
