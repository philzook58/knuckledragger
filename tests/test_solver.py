import kdrag
from kdrag.solvers import VampireTHFSolver, EProverTHFSolver
import kdrag.smt as smt
import kdrag.theories.real as real


def test_vampirethf():
    s = VampireTHFSolver()
    s.add(smt.BoolVal(True))
    assert s.check() == smt.sat

    s = VampireTHFSolver()
    s.add(smt.BoolVal(False))
    assert s.check() == smt.unsat

    s = VampireTHFSolver()
    p, q, r = smt.Bools("p q r")
    s.add(smt.Implies(p, q))
    s.add(p)
    s.add(smt.Not(q))
    assert s.check() == smt.unsat

    # extensionality`
    """ Need HO vampire
    s = VampireTHFSolver()
    S = smt.DeclareSort("S")
    T = smt.DeclareSort("T")
    x = smt.Const("x", S)
    f, g = smt.Consts("f g", S >> T)
    s.add(f == g)
    s.add(smt.Not(smt.ForAll([x], (f(x) == g(x)))))
    assert s.check() == smt.unsat

    x, y, z = smt.Reals("x y z")
    s = VampireTHFSolver()
    s.add(x + y == z)
    s.add(x == y)
    assert s.check() == smt.sat
    """

    s = EProverTHFSolver()
    S = smt.DeclareSort("S")
    T = smt.DeclareSort("T")
    x = smt.Const("x", S)
    f, g = smt.Consts("f g", S >> T)
    s.add(f == g)
    s.add(smt.Not(smt.ForAll([x], (f(x) == g(x)))))
    assert s.check() == smt.unsat

    s = EProverTHFSolver()
    f, g = smt.Consts("f g", S >> S)
    s.add(smt.Not(smt.Implies(smt.ForAll([x], (f(x) == x)), f == smt.Lambda([x], x))))
    assert s.check() == smt.unsat

    x, y, z = smt.Reals("x y z")
    s = EProverTHFSolver()
    s.add(real.abstract_arith(x + y == z))
    s.add(real.abstract_arith(x != z - y))
    s.add(real.sub_add.thm)
    assert s.check() == smt.unsat
