import pytest

from kdrag import prove
from kdrag.smt import ForAll, Lambda, Reals
from kdrag.theories.real import abs, has_diff_at, has_lim_at


@pytest.mark.parametrize("slope", [0, 1, 3])
def test_affine_derivative(slope):
    x, p, b = Reals("diff_x diff_p diff_b")
    f = Lambda(x, slope * x + b)
    prove(
        ForAll([p, b], has_diff_at(f, p, slope)),
        by=[has_diff_at.defn, has_lim_at.defn, abs.defn],
    )
