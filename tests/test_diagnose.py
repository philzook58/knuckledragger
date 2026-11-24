import pytest

import kdrag as kd
import kdrag.config as config
import kdrag.diagnose as diagnose
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
    # named as the Python variable (succ), not the z3 name (diag_succ)
    assert "countermodel\n✅ passes with by=[" in text
    assert text.endswith(".succ.defn]")


def test_diagnosis_can_be_switched_off(monkeypatch):
    monkeypatch.setattr(config, "diagnose", False)
    assert "✅" not in str(failure())


def test_prove_suggests_missing_definition_when_rendered(monkeypatch):
    repair = diagnose.repair
    attempts = []

    def record(*args, **kwargs):
        attempts.append(True)
        return repair(*args, **kwargs)

    monkeypatch.setattr(diagnose, "repair", record)
    with pytest.raises(kd.kernel.SolverFailure) as error:
        kd.prove(smt.ForAll([x], succ(x) > x))
    assert not attempts
    message = str(error.value)
    assert attempts
    assert "prove failed: z3 found a countermodel" in message
    assert "Countermodel:" not in message
    assert message.endswith(".succ.defn]")
