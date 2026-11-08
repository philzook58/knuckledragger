"""Regressions for dropped information and false solver success."""

import shutil
import subprocess

import pytest
import kdrag as kd
import kdrag.smt as smt
from kdrag.printers.smtlib import smtlib_problem
from kdrag.printers.tptp import expr_to_tptp
from kdrag.solvers import BaseSolver, CVC5Solver, VampireSolver, binpath


@pytest.mark.parametrize("format", ["tff", "thf"])
def test_nary_arithmetic(format):
    x, y, z = smt.Ints("x y z")
    assert expr_to_tptp(smt.Sum(x, y, z), format=format) == "$sum($sum(x,y),z)"
    assert (
        expr_to_tptp(smt.Product(x, y, z), format=format) == "$product($product(x,y),z)"
    )


@pytest.mark.slow
@pytest.mark.parametrize(
    "operation, correct, truncated", [(smt.Sum, 10, 5), (smt.Product, 30, 6)]
)
def test_tptp_arithmetic_counterexample(operation, correct, truncated):
    if not shutil.which(binpath("vampire")):
        pytest.skip("Vampire required")
    for value, status in [(correct, smt.unsat), (truncated, smt.sat)]:
        s = VampireSolver()
        s.set("format", "tff")
        s.add(smt.Not(operation(2, 3, 5) == value))
        assert s.check() == status


@pytest.mark.skipif(not shutil.which("cvc5"), reason="cvc5 required")
@pytest.mark.parametrize("feature", ["datatype", "bitvector", "sequence", "overload"])
def test_smt_builtin_semantics(feature):
    if feature == "datatype":
        D = smt.Datatype("CorrectnessDatatype")
        D.declare("zero")
        D.declare("succ", ("pred", D))
        D = D.create()
        thm = D.pred(D.succ(D.zero)) == D.zero
    elif feature == "bitvector":
        b = smt.BitVec("b", 16)
        thm = -(-b) == b
    elif feature == "sequence":
        S = smt.SeqSort(smt.IntSort())
        a = smt.Const("a", S)
        thm = smt.Concat(smt.Empty(S), a) == a
    else:
        i, r = smt.Int("same"), smt.Real("same")
        thm = smt.Implies(smt.And(i == 1, r == 2), smt.ToReal(i) < r)
    kd.prove(thm, solver=CVC5Solver)


def test_currying_preserves_binders():
    T = smt.IntSort()
    f = smt.Const("binary", smt.ArraySort(T, T, T))
    x, y = smt.Ints("x y")
    with pytest.raises(NotImplementedError, match="signatures"):
        BaseSolver().add(smt.ForAll([f], smt.Exists([x, y], f[x, y] == 0)))


def test_indexed_function_renaming():
    T = smt.IntSort()
    f = smt.Function("mapped", T, T)
    a = smt.Array("a", T, T)
    with pytest.raises(NotImplementedError, match="indexed operator"):
        smtlib_problem([smt.Map(f, a)[0] == f(a[0])])


def test_name_collisions(tmp_path):
    s = BaseSolver()
    s.add([smt.Int("same") == 1, smt.Real("same") == 2])
    with pytest.raises(ValueError, match="overloading"):
        s.write_tptp(tmp_path / "problem.p")
    s = BaseSolver()
    a, b = smt.Const("a", smt.DeclareSort("T")), smt.Const("b", smt.DeclareSort("t"))
    s.add([a == a, b == b])
    with pytest.raises(ValueError, match="sort-name collision"):
        s.write_tptp(tmp_path / "problem.p")


@pytest.mark.parametrize("name", ["Int", "Real", "Bool"])
def test_user_sort_is_not_a_builtin(tmp_path, name):
    T = smt.DeclareSort(name)
    x = smt.Const("x", T)
    s = BaseSolver()
    s.add(smt.ForAll([x], x == x))
    path = tmp_path / "problem.p"
    s.write_tptp(path)
    assert f"{name.lower()} : $tType" in path.read_text()


@pytest.mark.parametrize(
    "code, output", [(1, b"unsat\n"), (0, b"notunsat\n"), (0, b'(error "unsat")\n')]
)
def test_failed_output_is_not_a_proof(monkeypatch, code, output):
    monkeypatch.setattr(
        subprocess,
        "run",
        lambda *a, **kw: subprocess.CompletedProcess([], code, output, b""),
    )
    s = CVC5Solver()
    s.add(smt.BoolVal(True))
    assert s.check() == smt.unknown


def test_external_countermodel_without_model_api(monkeypatch):
    monkeypatch.setattr(
        subprocess,
        "run",
        lambda *a, **kw: subprocess.CompletedProcess([], 0, b"sat\n", b""),
    )
    with pytest.raises(kd.kernel.LemmaError, match="Countermodel"):
        kd.kernel.prove(smt.BoolVal(False), solver=CVC5Solver)
