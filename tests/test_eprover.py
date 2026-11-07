"""Exercise the packaged E binary without downloading other solvers."""

import subprocess
import sys

import pytest

import kdrag.smt as smt
from kdrag.solvers import EProverSolver, EProverTHFSolver


@pytest.mark.parametrize("solver", [EProverSolver, EProverTHFSolver])
def test_eprover_status(solver):
    s = solver()
    p, q = smt.Bools("p q")
    s.set("timeout", 2000)
    s.add(smt.And(p, q))
    # E's higher-order search is incomplete and can give up on SAT problems.
    expected = smt.sat if solver is EProverSolver else smt.unknown
    assert s.check() == expected
    s.add(smt.Not(p))
    assert s.check() == smt.unsat


def test_eprover_higher_order():
    s = EProverTHFSolver()
    domain = smt.DeclareSort("EProverDomain")
    x = smt.Const("x", domain)
    f, g = smt.Consts("f g", domain >> domain)
    s.set("timeout", 2000)
    s.add(f == g)
    s.add(smt.Not(smt.ForAll([x], f(x) == g(x))))
    assert s.check() == smt.unsat


def test_eprover_cli():
    result = subprocess.run(
        [sys.executable, "-m", "kdrag.solvers", "eprover", "--version"],
        capture_output=True,
        text=True,
        check=True,
    )
    assert "3.5.1" in result.stdout
