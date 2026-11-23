import pytest

from kdrag import prove
from kdrag.smt import ForAll, Lambda, Reals
from kdrag.theories.real import abs, has_lim_at
from kdrag.contrib.analysis.deriv import has_deriv_at


@pytest.mark.parametrize("slope", [0, 1, 3])
def test_affine_derivative(slope):
    x, p, b = Reals("diff_x diff_p diff_b")
    f = Lambda(x, slope * x + b)
    prove(
        ForAll([p, b], has_deriv_at(f, slope, p)),
        by=[has_deriv_at.defn, has_lim_at.defn, abs.defn],
    )
