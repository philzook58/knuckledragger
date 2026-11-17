import kdrag as kd
import kdrag.smt as smt
import kdrag.theories.real as real


def expand(expr):
    return smt.simplify(kd.rewrite.unfold(expr))


def test_intervals_and_balls():
    assert smt.is_true(expand(real.icc(0, 1)[0]))
    assert smt.is_false(expand(real.ioo(0, 1)[0]))
    assert smt.is_false(expand(real.icc(1, 0)[0]))
    assert smt.is_true(expand(real.ball(3, 2)[4]))
    assert smt.is_false(expand(real.ball(3, 2)[5]))
    assert smt.is_false(expand(real.ball(3, 0)[3]))
    assert smt.is_false(expand(real.ball(3, -1)[3]))


def test_indexed_set_operations():
    # Negative entries must not participate in either operation.
    family = smt.Store(smt.K(smt.IntSort(), real.empty), -1, real.univ)
    union = expand(real.iunion(family)[0])
    solver = smt.Solver()
    solver.add(union)
    assert solver.check() == smt.unsat
    family = smt.Store(smt.K(smt.IntSort(), real.univ), -1, real.empty)
    inter = expand(real.iinter(family)[0])
    solver = smt.Solver()
    solver.add(smt.Not(inter))
    assert solver.check() == smt.unsat


def test_bounds_definitions():
    singleton = smt.Lambda(real.x, real.x == 2)
    assert expand(real.upper_bounds(singleton)[3]).eq(
        smt.simplify(smt.ForAll(real.x, real.x == 2, real.x <= 3)))
    assert expand(real.lower_bounds(singleton)[1]).eq(
        smt.simplify(smt.ForAll(real.x, real.x == 2, 1 <= real.x)))


def test_interior_point_does_not_capture_radius():
    radius = smt.Real("eps")
    condition = real.interior_point(real.ball(0, radius), radius)
    assert radius in kd.utils.free_vars(condition)
    assert smt.is_quantifier(condition) and condition.is_exists()
