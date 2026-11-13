import shutil
import subprocess

import pytest

from kdrag import smt
from kdrag.printers.lean import guard_prop, of_prop
from kdrag.solvers import LeanSolver


def test_prop_names():
    x = smt.Int("x")
    pred = smt.Function("Spec.pred!", smt.IntSort(), smt.BoolSort())
    # The inner binder and the free constant share the outer binder's spelling.
    expr = smt.And(
        pred(x),
        smt.ForAll(x, smt.Implies(pred(x), smt.Exists(x, pred(x)))),
    )
    assert of_prop(expr) == (
        "Spec.«pred!» x ∧ (∀ (x_1 : Int), Spec.«pred!» x_1 → "
        "(∃ (x_2 : Int), Spec.«pred!» x_2))"
    )


def test_prop_rejects_unsupported_terms():
    with pytest.raises(TypeError, match="Expected a Boolean"):
        of_prop(smt.IntVal(0))
    x = smt.BitVec("x", 8)
    with pytest.raises(NotImplementedError, match="BitVec"):
        of_prop(x == 0)
    a = smt.Array("a", smt.IntSort(), smt.IntSort())
    with pytest.raises(NotImplementedError, match="store"):
        of_prop(smt.Store(a, 0, 1) == a)
    x, y = smt.Reals("x y")
    with pytest.raises(NotImplementedError, match="operator: /"):
        of_prop(x / y == 0)
    with pytest.raises(ValueError, match="Ambiguous Lean name x"):
        of_prop(smt.And(smt.Int("x") == 0, smt.Real("x") == 0))


def test_prop_guard_in_lean():
    if shutil.which("elan") is None:
        pytest.skip("Lean toolchain manager is unavailable")
    lean = ["elan", "run", LeanSolver().lean_version, "lean", "--stdin"]
    x, y, z = smt.Ints("x y z")
    p, q, r = smt.Bools("p q r")
    f = smt.Function("f", smt.IntSort(), smt.IntSort(), smt.IntSort())
    pred = smt.Function("Spec.pred!", smt.BoolSort(), smt.IntSort(), smt.BoolSort())
    u = smt.DeclareSort("U")
    a = smt.Const("a", u)
    g = smt.Function("g", u, u)
    v = smt.DeclareSort("V")
    b = smt.Const("b", v)
    cases = [
        (x - (y - z) == (x + y) * z, "(x - (y - z)) = ((x + y) * z)"),
        (smt.Implies(smt.Implies(p, q), r), "(p → q) → r"),
        (smt.And(smt.Or(p, q), smt.Not(r), p == q), "(p ∨ q) ∧ (¬ r ∧ (p ↔ q))"),
        (smt.And(smt.And(), smt.Or()), "True ∧ False"),
        (
            smt.ForAll(x, smt.Exists(y, smt.Lambda(z, z + x)[y] == f(x, y))),
            "∀ (x : Int), ∃ (y : Int), (fun (z : Int) => z + x) y = f x y",
        ),
        (
            pred(smt.Not(p), f(x, smt.If(q, y, -z))),
            "Spec.«pred!» (¬ p) (f x (if q then y else -z))",
        ),
        (-(-x) == -(y + z), "-(-x) = -(y + z)"),
        (
            smt.And(g(a) == a, smt.ForAll(a, g(a) == a)),
            "Nonempty U → g a = a ∧ (∀ (b : U), g b = b)",
        ),
        (
            smt.Exists([a, b], a == a) == p,
            "Nonempty U → Nonempty V → ((∃ (a : U) (b : V), a = a) ↔ p)",
        ),
    ]
    prelude = """open Classical
namespace Spec
abbrev «pred!» (p : Prop) (x : Int) : Prop := p ∧ x > 0
end Spec
variable (x y z : Int) (p q r : Prop) (f : Int → Int → Int)
variable (U : Type) (a : U) (g : U → U)
variable (V : Type)
"""
    source = [prelude]
    for expr, expected in cases:
        for width in (24, 100):
            source.append(guard_prop(expr, width=width))
            source.append(f"#guard_expr ({of_prop(expr, width=width)}) =ₐ ({expected})")
    prop = of_prop(smt.ForAll(x, smt.Implies(x > 0, x + 1 > 0)), width=24)
    source.append(f"example : ({prop}) := by\n  intro x hx\n  omega")
    witness = of_prop(smt.Exists(a, a == a))
    source.append(f"example : ({witness}) := by\n  intro ⟨b⟩\n  exact ⟨b, rfl⟩")
    result = subprocess.run(
        lean, input="\n".join(source), capture_output=True, text=True, timeout=30
    )
    assert result.returncode == 0, result.stdout + result.stderr

    # Both sides elaborate, but subtraction without parentheses associates left.
    expected = of_prop(cases[0][0], fully_parenthesized=True)
    result = subprocess.run(
        lean,
        input=prelude + f"#guard_expr (x - y - z = (x + y) * z) =ₐ ({expected})",
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert result.returncode != 0
    assert "failed" in result.stdout
