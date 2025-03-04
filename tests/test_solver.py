import pytest
import kdrag as kd
from kdrag.solvers import (
    VampireTHFSolver,
    EProverTHFSolver,
    MultiSolver,
    ZipperpositionSolver,
    TweeSolver,
    SATSolver,
)
import kdrag.solvers as solvers
import kdrag.smt as smt
import kdrag.theories.real as real
import shutil
from kdrag.solvers.egglog import EgglogSolver
import kdrag.solvers.gappa as gappa
import kdrag.solvers.aprove


@pytest.mark.slow
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

    if shutil.which("zipperposition") is not None:
        s = ZipperpositionSolver()
        s.add(smt.BoolVal(True))
        assert s.check() == smt.unknown

    # s = MultiSolver()
    # s.add(smt.BoolVal(True))

    # Does not pass. TODO: Need to fix intrinsics
    # kd.prove(smt.Or(smt.BoolVal(False), smt.BoolVal(True)), solver=EProverTHFSolver)

    kd.kernel.prove(
        smt.Or(smt.BoolVal(False), smt.BoolVal(True)), solver=EProverTHFSolver
    )

    # https://www.cl.cam.ac.uk/~jrh13/hol-light/manual-1.1.pdf
    kd.kernel.prove(
        smt.Lambda([x], x) == smt.Lambda([y], y),
        solver=EProverTHFSolver,
    )

    kd.kernel.prove(smt.Lambda([x], x) == smt.Lambda([y], y))

    f = smt.Const("f", smt.BoolSort() >> smt.BoolSort())
    p, q = smt.Bools("p q")

    kd.kernel.prove(
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
    kd.kernel.prove(
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
    kd.kernel.prove(
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
    
    kd.kernel.prove(
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


@pytest.mark.slow
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
    if shutil.which("zipperposition") is not None:
        assert check(ZipperpositionSolver()) == smt.unsat
    assert check(smt.Solver()) == smt.unsat
    assert check(solvers.VampireSolver()) == smt.unsat


def test_egglog():
    e = EgglogSolver(debug=True)
    x, y, z = smt.Consts("x y z", smt.IntSort())
    f = smt.Function("f", smt.IntSort(), smt.IntSort())
    e.add(x == y)
    e.add(smt.ForAll([x], f(x) == f(f(y))))
    e.let("t", f(f(x)))
    e.run(10)
    assert e.extract(f(x)) == ["(f (x))"]


def test_satsolver():
    s = SATSolver()
    x, y, z = smt.Bools("x y z")
    s.add(x == y)
    s.add(y == z)
    assert s.check() == smt.sat
    s.add(x != z)
    assert s.check() == smt.unsat


def test_vampire_question_answer():
    s = solvers.VampireSolver()
    x, y, z = smt.Ints("x y z")
    res = s.query(smt.Exists([x], x > 3))
    assert len(res) == 1
    assert "% SZS answers Tuple" in s.res.stdout.decode()
    T = smt.DeclareSort("T")
    y = smt.Const("y", T)
    f = smt.Function("f", T, smt.BoolSort())
    s = solvers.VampireSolver()
    s.add(f(y))
    res = s.query(smt.Exists([y], f(y)))
    assert re.fullmatch(
        r"\% SZS answers Tuple \[\[y_[0-9a-f]*\]\|_\] for vampire", res[0]
    )


def test_gappa():
    x, y = smt.Reals("x y")
    assert (
        gappa.gappa_of_bool(smt.Implies(smt.And(x <= 2, x >= -2 / 8), x * x <= 4))
        == "(((x <= 2) /\\ (x >= -0.25)) -> ((x * x) <= 4))"
    )
    s = gappa.GappaSolver()
    s.add(smt.Implies(smt.And(x <= 2, x >= -1 / 128), x * x <= 4))
    s.check()
    s.bound(x * x)


import re


def test_fof():
    x = smt.Int("x")
    assert re.match(
        r"\(!\[Xbang[0-9]+_(?P<var_num>[a-zA-Z0-9]+)\] : \(\$greater\(Xbang[0-9]+_(?P=var_num),4\) & \$lesseq\(Xbang[0-9]+_(?P=var_num),7\)\)\)",
        kd.solvers.expr_to_tptp(smt.ForAll([x], smt.And(x > 4, x <= 7)), format="fof"),
    )


def test_tptp():
    x = smt.Int("x")
    assert (
        re.match(
            r"\(\$greater\(x_[0-9a-f]+,4\) & \$lesseq\(x_[0-9a-f]+,7\)\)",
            kd.solvers.expr_to_tptp(smt.And(x > 4, x <= 7)),
        )
        is not None
    )
    assert kd.solvers.sort_to_tptp(smt.IntSort()) == "$int"
    assert kd.solvers.sort_to_tptp(smt.BoolSort()) == "$o"
    assert (
        kd.solvers.sort_to_tptp(
            smt.ArraySort(smt.ArraySort(smt.BoolSort(), smt.IntSort()), smt.IntSort())
        )
        == "(($o > $int) > $int)"
    )


"""
TODO: Not installing aprove in CI?
def test_aprove():
    plus = smt.Function("plus", smt.IntSort(), smt.IntSort(), smt.IntSort())
    x, y, z = smt.Ints("x y z")
    succ = smt.Function("succ", smt.IntSort(), smt.IntSort())
    zero = smt.IntVal(0)
    kd.solvers.aprove.run_aprove(
        [x, y], [plus(x, zero) == x, plus(x, succ(y)) == succ(plus(x, y))]
    )
"""
