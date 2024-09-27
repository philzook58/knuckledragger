import kdrag as kd
from kdrag.solvers import (
    VampireTHFSolver,
    EProverTHFSolver,
    MultiSolver,
    ZipperpositionSolver,
    TweeSolver,
)
import kdrag.solvers as solvers
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

    S = smt.DeclareSort("S")
    T = smt.DeclareSort("T")
    x, y, z = smt.Consts("x y z", S)
    f, g = smt.Consts("f g", S >> T)

    """
    s = VampireTHFSolver()
    s.add(f == g)
    s.add(smt.Not(smt.ForAll([x], (f(x) == g(x)))))
    assert s.check() == smt.unsat
    """
    s = EProverTHFSolver()
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

    s = MultiSolver()
    s.add(smt.BoolVal(False))
    assert s.check() == smt.unsat

    s = ZipperpositionSolver()
    s.add(smt.BoolVal(True))
    assert s.check() == smt.unknown

    # s = MultiSolver()
    # s.add(smt.BoolVal(True))

    # Does not pass. TODO: Need to fix intrinsics
    # kd.lemma(smt.Or(smt.BoolVal(False), smt.BoolVal(True)), solver=EProverTHFSolver)

    kd.kernel.lemma(
        smt.Or(smt.BoolVal(False), smt.BoolVal(True)), solver=EProverTHFSolver
    )

    # https://www.cl.cam.ac.uk/~jrh13/hol-light/manual-1.1.pdf
    kd.kernel.lemma(
        smt.Lambda([x], x) == smt.Lambda([y], y),
        solver=EProverTHFSolver,
    )

    kd.kernel.lemma(smt.Lambda([x], x) == smt.Lambda([y], y))

    f = smt.Const("f", smt.BoolSort() >> smt.BoolSort())
    p, q = smt.Bools("p q")

    kd.kernel.lemma(
        smt.ForAll(
            [p],
            p == (smt.Lambda([f], f(p)) == smt.Lambda([f], f(smt.BoolVal(True)))),
        ),
        solver=EProverTHFSolver,
    )

    s = TweeSolver()
    x, y, z = smt.Consts("x y z", S)
    s.add(x == y)
    s.add(y == z)
    s.add(smt.Not(x == z))
    s.check()
    """
    f = smt.Const("f", smt.BoolSort() >> (smt.BoolSort() >> smt.IntSort()))
    kd.kernel.lemma(
        smt.ForAll(
            [p, q],
            smt.And(p, q)
            == (
                smt.Lambda([f], f(p)(q))
                == smt.Lambda([f], f(smt.BoolVal(True))(smt.BoolVal(True)))
            ),
        ),
        solver=EProverTHFSolver,
    )
    """
    """
    kd.kernel.lemma(
        kd.QForAll(
            [p, q],
            smt.And(p, q)
            == (
                smt.ForAll([f], f(p)(q))
                == smt.ForAll([f], f(smt.BoolVal(True))(smt.BoolVal(True)))
            ),
        ),
        solver=EProverTHFSolver,
    )
    
    kd.kernel.lemma(
        kd.QForAll(
            [p, q],
            smt.And(p, q),
            smt.Lambda([f], f(p)(q))
            == smt.Lambda([f], f(smt.BoolVal(True))(smt.BoolVal(True))),
        ),
        solver=EProverTHFSolver,
    )
    """

    """
    % TPTP file generated by Knuckledragger
    % Declarations
    % Axioms and assertions

    thf(d1, type, a : $i).
    thf(d2, type, b : $i).
    thf(ax, axiom, a != b).
    thf(ax, axiom, ![X : $i] : ((X = a) | (X = b))).
    thf(ax_0, axiom, ~((![P_123:$o] : (P_123 = ((^[F_120:($o > $i)] : (F_120 @ P_123)) = (^[F_120:($o > $i)] : (F_120 @ $true))))))).

    %thf(ax_0, axiom, ~((![P_123:$o] : (P_123 = ((^[F_120:($o > $o)] : (F_120 @ P_123)) = (^[F_120:($o > $o)] : (F_120 @ $true))))))).
    %thf(ax_0, axiom, ~((![P_123:$o] : (P_123 = ((![F_120:($o > $o)] : ((F_120 @ P_123) = (F_120 @ $true)))))))).
    %thf(ax_0, axiom, ~((![P_123:$o] : (P_123 = ((![F_120:($o > $i)] : ((F_120 @ P_123) = (F_120 @ $true)))))))).
    
    %  --mode {best|fo-complete-basic|ho-comb-complete|ho-competitive
    %|ho-complete-basic|ho-pragmatic|lambda-free-extensional|lambda-free-intensional|lambda-free-purify-extensional|lambda-free-purify-intensional}
    """


"""
TODO: Yeah, the entire refutation idea doesn't work here.
def test_nanocopi():
    s = solvers.NanoCopISolver()
    p, q, r = smt.Bools("p q r")
    s.add(smt.Or(p, smt.Not(p)))
    assert s.check() == smt.unsat
"""


def test_tao():
    # https://www.philipzucker.com/tao_algebra/
    T = smt.DeclareSort("T")
    x, y, z = smt.Consts("x y z", T)
    mul = smt.Function("mul", T, T, T)
    kd.notation.mul.define([x, y], mul(x, y))

    def check(s):
        s.add(smt.ForAll([x, y], (x * x) * y == y * x))
        s.add(smt.Not(smt.ForAll([x, y], x * y == y * x)))
        return s.check()

    assert check(TweeSolver()) == smt.unsat
    assert check(VampireTHFSolver()) == smt.unsat
    assert check(EProverTHFSolver()) == smt.unsat
    assert check(MultiSolver()) == smt.unsat
    assert check(ZipperpositionSolver()) == smt.unsat
    assert check(smt.Solver()) == smt.unsat
    assert check(solvers.VampireSolver()) == smt.unsat
