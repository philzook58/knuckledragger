import pytest

import kdrag as kd
import kdrag.smt as smt
from kdrag.solvers import VampireSolver, EProverSolver


@pytest.mark.parametrize("solver", ["vampire", "eprover", VampireSolver, EProverSolver])
def test_prove_with_solver(solver):
    p, q = smt.Bools("p q")
    thm = smt.Implies(smt.And(p, q), p)
    assert kd.prove(thm, solver=solver).thm.eq(thm)
    with pytest.raises(kd.kernel.LemmaError, match="Countermodel"):
        kd.prove(smt.BoolVal(False), solver=solver)


def test_prove_rejects_unknown_solver_name():
    with pytest.raises(ValueError, match="Unknown solver 'vamprie'"):
        kd.prove(smt.BoolVal(True), solver="vamprie")
