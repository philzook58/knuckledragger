"""Exercise the packaged Vampire binary without downloading other solvers."""

import subprocess
import sys

import pytest

import kdrag.smt as smt
from kdrag.solvers import VampireSolver, VampireTHFSolver, run


@pytest.mark.parametrize("format", ["smtlib2", "tff", "thf"])
def test_vampire_status(format):
    s = VampireSolver()
    s.set("format", format)
    s.set("timeout", 2000)
    p, q = smt.Bools("p q")
    s.add(smt.And(p, q))
    # Higher-order search can give up on satisfiable problems.
    expected = smt.unknown if format == "thf" else smt.sat
    assert s.check() == expected
    s.add(smt.Not(p))
    assert s.check() == smt.unsat


def test_vampire_higher_order():
    s = VampireTHFSolver()
    domain = smt.DeclareSort("VampireDomain")
    x = smt.Const("x", domain)
    f, g = smt.Consts("f g", domain >> domain)
    s.set("timeout", 2000)
    s.add(f == g)
    s.add(smt.Not(smt.ForAll([x], f(x) == g(x))))
    assert s.check() == smt.unsat


@pytest.mark.parametrize("command", ["vampire", "vampire-ho"])
def test_vampire_cli(command):
    result = subprocess.run(
        [sys.executable, "-m", "kdrag.solvers", command, "--version"],
        capture_output=True,
        text=True,
        check=True,
    )
    assert "Vampire 5.1.0" in result.stdout
    result = run(command, ["--version"], capture_output=True, text=True, check=True)
    assert "Vampire 5.1.0" in result.stdout
