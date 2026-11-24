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


def test_prove_diagnoses_failure_with_assumptions():
    local = kd.FreshVar("local", smt.IntSort())
    goal = succ(local) > 0
    with pytest.raises(kd.kernel.SolverFailure) as error:
        kd.prove(goal, fixes=[local], assumes=[local >= 0])
    text = str(error.value)
    assert text.index("0: local₀ ≥ 0") < text.index("⊢ diag_succ(local₀) > 0")
    assert "prove failed: z3 found a countermodel" in text
    assert "Countermodel:" in text
    assert text.endswith(".succ.defn]")
    assert error.value.args[1] == "Countermodel"
    proof = kd.prove(goal, fixes=[local], assumes=[local >= 0], by=succ.defn)
    assert isinstance(proof.thm, smt.QuantifierRef) and proof.thm.is_forall()


def test_prove_repairs_are_lazy_and_can_be_disabled(monkeypatch):
    calls = []

    def repair(*args, **kwargs):
        calls.append((args, kwargs))
        return [succ.defn]

    monkeypatch.setattr(diagnose, "repair", repair)
    with pytest.raises(kd.kernel.SolverFailure) as error:
        kd.prove(succ(x) > x, solver="z3")
    assert not calls
    monkeypatch.setattr(config, "diagnose", False)
    assert "passes with by=" not in str(error.value)
    assert not calls
    monkeypatch.setattr(config, "diagnose", True)
    assert str(error.value).endswith(".succ.defn]")
    assert calls[0][1]["solver"] == "z3"


def test_prove_diagnoses_a_solver_timeout(monkeypatch):
    def timeout(*args, **kwargs):
        raise TimeoutError("solver timeout")

    monkeypatch.setattr(kd.kernel, "prove", timeout)
    monkeypatch.setattr(config, "diagnose", False)
    with pytest.raises(TimeoutError, match="prove failed: timed out after 12ms"):
        kd.prove(succ(x) > x, timeout=12)
