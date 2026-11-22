import pytest

import kdrag as kd
import kdrag.smt as smt
from kdrag.tactics import _AutoFailure

x = smt.Int("x")
succ = kd.define("diag_succ", [x], x + 1)


def failure() -> _AutoFailure:
    l = kd.Lemma(smt.ForAll([x], succ(x) > x))
    l.fix()
    with pytest.raises(_AutoFailure) as e:
        l.auto()
    return e.value


def test_failure_suggests_missing_definition():
    text = str(failure())
    # goal first, then the failure, then the repair
    assert text.index("⊢ diag_succ(x₀) > x₀") < text.index(
        "❌ auto failed: z3 found a countermodel"
    )
    assert "countermodel\n✅ passes adding diag_succ.defn" in text


def test_diagnosis_can_be_switched_off():
    kd.config.diagnose = False
    try:
        assert "✅" not in str(failure())
    finally:
        kd.config.diagnose = True
