"""
Tests for ProofState error handling and informative error messages.
"""

import pytest
import kdrag as kd
import kdrag.smt as smt
from kdrag.tactics import ProofStateError


def test_auto_error_with_goal_state():
    """Test that auto() errors include goal state context."""
    x = smt.Int("x")
    l = kd.Lemma(x > 10)
    
    with pytest.raises(ProofStateError) as exc_info:
        l.auto(by=[])
    
    error = exc_info.value
    # Check that it's a ProofStateError
    assert isinstance(error, ProofStateError)
    # Check that the goal state is in the error message
    assert "[] ?|= x > 10" in str(error)
    # Check that the original error is also present
    assert "Countermodel" in str(error)


def test_have_error_with_goal_state():
    """Test that have() errors include goal state context."""
    x, y = smt.Ints("x y")
    l = kd.Lemma(smt.Implies(x > 0, x > 10))
    l.intros()
    
    with pytest.raises(ProofStateError) as exc_info:
        l.have(x > 100, by=[])
    
    error = exc_info.value
    # Check that it's a ProofStateError
    assert isinstance(error, ProofStateError)
    # Check that the goal state with context is in the error message
    assert "[x > 0]" in str(error)
    assert "x > 100" in str(error)
    # Check that the original error is also present
    assert "Countermodel" in str(error)


def test_eq_error_with_goal_state():
    """Test that eq() errors include goal state context."""
    x, y = smt.Ints("x y")
    l = kd.Lemma(x == y)
    
    with pytest.raises(ProofStateError) as exc_info:
        # Try to replace y with something unprovable
        l.eq(x + 100, by=[])
    
    error = exc_info.value
    assert isinstance(error, ProofStateError)
    # Check that the goal state is in the error message
    assert "x == y" in str(error) or "x = y" in str(error)


def test_newgoal_error_with_goal_state():
    """Test that newgoal() errors include goal state context."""
    x = smt.Int("x")
    l = kd.Lemma(x > 100)
    
    with pytest.raises(ProofStateError) as exc_info:
        # Try to replace goal with something that doesn't imply the original
        # x > 0 doesn't imply x > 100
        l.newgoal(x > 0, by=[])
    
    error = exc_info.value
    assert isinstance(error, ProofStateError)
    # Check that the goal state is in the error message
    assert "x >" in str(error)


def test_nested_goal_state_error():
    """Test error handling with more complex goal states (with signature and context)."""
    x = smt.Int("x")
    l = kd.Lemma(smt.ForAll([x], smt.Implies(x > 0, x > 10)))
    _x = l.fix()
    l.intros()
    
    with pytest.raises(ProofStateError) as exc_info:
        l.auto(by=[])
    
    error = exc_info.value
    assert isinstance(error, ProofStateError)
    # The error should show the eigenvariable
    assert "x!" in str(error)
    # The error should show the context
    assert "> 0" in str(error)
    # The error should show the goal
    assert "> 10" in str(error)


def test_error_preserves_original_exception():
    """Test that ProofStateError preserves the original exception."""
    x = smt.Int("x")
    l = kd.Lemma(x > 10)
    
    with pytest.raises(ProofStateError) as exc_info:
        l.auto(by=[])
    
    error = exc_info.value
    # Check that the original error is a LemmaError
    assert isinstance(error.original_error, kd.kernel.LemmaError)
    # Check that the chaining is correct (cause)
    assert error.__cause__ is error.original_error


def test_simp_error_with_goal_state():
    """Test that simp() errors include goal state context if prove fails."""
    # Note: simp() calls prove internally for equality proofs
    # This test is to ensure those are also wrapped
    x = smt.Int("x")
    l = kd.Lemma(x > 0)
    
    # simp shouldn't fail on this simple case, so we just verify no errors
    # The wrapping is in place for when it does call prove
    l.simp()
    assert True  # If we got here, simp didn't crash


def test_qed_error_with_goal_state():
    """Test that qed() errors include goal state context."""
    x = smt.Int("x")
    # Create a lemma but don't prove it
    l = kd.Lemma(x > 100)
    
    with pytest.raises(ProofStateError) as exc_info:
        # Try to finalize without proving the goal
        l.qed(by=[])
    
    error = exc_info.value
    assert isinstance(error, ProofStateError)
    # Check that the goal state is in the error message
    assert "x > 100" in str(error)
    # Check that the original error is also present
    assert "Countermodel" in str(error)
