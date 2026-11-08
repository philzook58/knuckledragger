"""Replay library proofs and exercise the external-solver failure path."""

import shutil
import subprocess
import sys

import pytest

import kdrag as kd
import kdrag.smt as smt
from kdrag.printers.smtlib import smtlib_problem
from kdrag.printers.tptp import expr_to_tptp
from kdrag.solvers import (
    CVC5Solver,
    EProverSolver,
    SolverError,
    VampireSolver,
    binpath,
    run_solver,
    smt_status,
)


@pytest.mark.skipif(shutil.which("cvc5") is None, reason="cvc5 executable required")
@pytest.mark.parametrize(
    "feature", ["datatype", "bitvector", "sequence", "overload", "lambda", "names"]
)
def test_cvc5_native_printer(feature):
    x, y = smt.Ints("x y")
    if feature == "datatype":
        D = smt.Datatype("PrinterDatatype")
        D.declare("zero")
        D.declare("succ", ("pred", D))
        D = D.create()
        thm = D.pred(D.succ(D.zero)) == D.zero
    elif feature == "bitvector":
        b = smt.BitVec("b", 16)
        thm = smt.And(-(-b) == b, smt.Extract(7, 0, b) == smt.Extract(7, 0, b))
    elif feature == "sequence":
        S = smt.SeqSort(smt.IntSort())
        a = smt.Const("a", S)
        thm = smt.Concat(smt.Empty(S), a) == a
    elif feature == "overload":
        i, r = smt.Int("overloaded"), smt.Real("overloaded")
        thm = smt.Implies(smt.And(i == 1, r == 2), smt.ToReal(i) < r)
    elif feature == "lambda":
        thm = smt.Lambda([x, y], x + y)[x, y] == x + y
    else:
        f = smt.Function("space and.dot", smt.IntSort(), smt.IntSort())
        thm = smt.Implies(x == y, f(x) == f(y))
    kd.prove(thm, solver=CVC5Solver)
    # A printer must preserve counterexamples too, not just prove tautologies.
    s = CVC5Solver()
    s.add(smt.And(thm, x != y))
    assert s.check() != smt.unsat


def test_printer_rejects_unrenamed_indexed_function():
    T = smt.IntSort()
    f = smt.Function("mapped_function", T, T)
    a = smt.Array("a", T, T)
    with pytest.raises(NotImplementedError, match="indexed operator"):
        smtlib_problem([smt.Map(f, a)[0] == f(a[0])])


def test_rejects_quantified_multidomain_array():
    T = smt.IntSort()
    f = smt.Const("binary", smt.ArraySort(T, T, T))
    x, y = smt.Ints("x y")
    thm = smt.ForAll([f], smt.Exists([x, y], f[x, y] == 0))
    # Currying only the body leaves the curried f free under the old binder.
    with pytest.raises(NotImplementedError, match="signature"):
        CVC5Solver().add(thm)
    consumer = smt.Function("binary_consumer", f.sort(), T)
    with pytest.raises(NotImplementedError, match="signature"):
        CVC5Solver().add(consumer(smt.Lambda([x, y], x + y)) == 0)


@pytest.mark.xfail(
    strict=True,
    reason="TPTP printer drops operands after the second in n-ary arithmetic",
)
def test_tptp_nary_sum_gap():
    x, y, z = smt.Ints("printer_x printer_y printer_z")
    assert "printer_z" in expr_to_tptp(smt.Sum(x, y, z))


@pytest.mark.slow
@pytest.mark.xfail(
    strict=True, reason="TPTP printer does not quote dotted declaration names"
)
def test_eprover_dotted_name_gap():
    pytest.importorskip("eprover")
    T = smt.DeclareSort("PrinterDomain")
    x, y = smt.Consts("x y", T)
    f = smt.Function("namespace.function", T, T)
    kd.prove(
        smt.ForAll([x, y], smt.Implies(x == y, f(x) == f(y))), solver=EProverSolver
    )


@pytest.mark.skipif(shutil.which("cvc5") is None, reason="cvc5 executable required")
@pytest.mark.xfail(
    strict=True, reason="Z3 set-as-array operators need lowering for cvc5"
)
def test_cvc5_set_operator_gap():
    T = smt.IntSort()
    A = smt.Const("set_A", smt.SetSort(T))
    kd.prove(smt.ForAll([A], smt.SetUnion(A, smt.EmptySet(T)) == A), solver=CVC5Solver)


@pytest.mark.slow
def test_replay_group_with_eprover():
    pytest.importorskip("eprover")
    import kdrag.theories.algebra.group as group

    kd.prove(
        group.id_right.thm,
        by=[group.mul_assoc, group.id_left, group.inv_left],
        solver=EProverSolver,
    )


@pytest.mark.slow
def test_replay_kleene_with_vampire():
    if not shutil.which(binpath("vampire")):
        pytest.skip("Vampire executable required")
    import kdrag.theories.algebra.kleene as kleene

    kd.prove(
        kleene.zero_par.thm, by=[kleene.par_comm, kleene.par_zero], solver=VampireSolver
    )


class UnknownZ3(smt.Z3Solver):
    def check(self):
        return smt.unknown


def force_z3_unknown(monkeypatch):
    monkeypatch.setattr(kd.tactics, "Z3Solver", UnknownZ3)
    monkeypatch.setattr(kd.config, "solver", UnknownZ3)


@pytest.mark.skipif(shutil.which("cvc5") is None, reason="cvc5 executable required")
def test_automatic_fallback_preserves_premises(monkeypatch):
    x = smt.Int("fallback_x")
    f = kd.define("test_fallback_function", [x], x + 1)
    force_z3_unknown(monkeypatch)
    pf = kd.prove(f(0) == 1, by=[f.defn])
    assert pf.thm.eq(f(0) == 1)
    assert "CVC5Solver" in pf.reason


def test_fallback_disabled_or_explicit_solver(monkeypatch):
    force_z3_unknown(monkeypatch)
    with pytest.raises(kd.kernel.SolverUnknown):
        kd.prove(smt.BoolVal(True), fallback=[])
    with pytest.raises(kd.kernel.SolverUnknown):
        kd.prove(smt.BoolVal(True), solver=UnknownZ3)


def test_no_fallback_after_countermodel():
    def must_not_run():
        raise AssertionError("fallback should not run after sat")

    with pytest.raises(kd.kernel.LemmaError, match="Countermodel"):
        kd.prove(smt.BoolVal(False), fallback=[must_not_run])


def test_fallback_failure_preserves_diagnostics(monkeypatch):
    force_z3_unknown(monkeypatch)

    def broken():
        raise SolverError("unsupported input")

    with pytest.raises(kd.kernel.SolverUnknown) as exc:
        kd.prove(smt.BoolVal(True), fallback=[broken])
    assert "unsupported input" in " ".join(exc.value.__notes__)


def test_cvc5_parse_error_is_not_unknown(monkeypatch):
    def error(*args):
        return subprocess.CompletedProcess(
            [], 1, b'(error "unsupported operator")', b""
        )

    monkeypatch.setattr(kd.solvers, "run_solver", error)
    s = CVC5Solver()
    s.add(smt.BoolVal(True))
    with pytest.raises(SolverError, match="unsupported operator"):
        s.check()


def test_external_process_wall_timeout():
    result = run_solver([sys.executable, "-c", "import time; time.sleep(10)"], 10)
    assert result.returncode != 0
    assert smt_status(result) == smt.unknown
