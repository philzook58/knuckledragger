import pytest

import kdrag as kd
import kdrag.smt as smt
import kdrag.theories.real as real
from kdrag.theories.real.cont import has_lim_at_add, has_lim_at_mul


def test_limits_at_removable_discontinuities():
    # The values at zero differ from the limits, so continuity cannot be assumed.
    zero, two, three = smt.RealVal(0), smt.RealVal(2), smt.RealVal(3)
    f = smt.Store(smt.K(smt.RealSort(), two), zero, 1)
    g = smt.Store(smt.K(smt.RealSort(), three), zero, 4)
    lf = kd.prove(
        real.has_lim_at(f, zero, two), by=[real.has_lim_at.defn, real.abs.defn]
    )
    lg = kd.prove(
        real.has_lim_at(g, zero, three), by=[real.has_lim_at.defn, real.abs.defn]
    )
    sum_limit = has_lim_at_add(f, g, zero, two, three)(lf, lg)
    product_limit = has_lim_at_mul(f, g, zero, two, three)(lf, lg)
    assert smt.simplify(sum_limit.thm).eq(smt.simplify(real.has_lim_at(f + g, zero, 5)))
    assert smt.simplify(product_limit.thm).eq(
        smt.simplify(real.has_lim_at(f * g, zero, 6))
    )


@pytest.mark.parametrize("module", ["cont", "lim_algebra"])
def test_analysis_proofs(module):
    import runpy
    import kdrag.config as config
    import kdrag.theories.real.seq  # Load dependencies before measuring the lemmas.

    was_timing = config.timing
    start = len(config.perf_log)
    try:
        config.timing = True
        runpy.run_path(f"src/kdrag/theories/real/{module}.py")
        timings = config.perf_log[start:]
    finally:
        config.timing = was_timing
        del config.perf_log[start:]

    solves = [(thm, elapsed) for tag, thm, elapsed in timings if tag == "solver.check"]
    assert solves
    durations = [elapsed for _, elapsed in solves]
    print(
        f"Z3 checks: {len(solves)}, total {sum(durations):.4f}s, max {max(durations):.4f}s"
    )
    for thm, elapsed in solves:
        assert elapsed < 0.5, ("solver.check", thm, elapsed)
