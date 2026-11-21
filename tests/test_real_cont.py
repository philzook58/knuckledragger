import pytest
import subprocess
import sys

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
    # Pointwise addition creates fresh lambda binders on each call, so compare
    # the proven proposition semantically rather than requiring identical ASTs.
    kd.prove(real.has_lim_at(f + g, zero, 5), by=[sum_limit])
    assert smt.simplify(product_limit.thm).eq(
        smt.simplify(real.has_lim_at(f * g, zero, 6))
    )


@pytest.mark.parametrize("module", ["cont", "rseq"])
def test_analysis_proofs(module):
    # Import in a fresh process: re-executing rseq would redefine its chosen lim.
    subprocess.run(
        [sys.executable, "-c", """
import importlib
import sys
import kdrag.config as config
import kdrag.theories.real
import kdrag.theories.int

config.timing = True
importlib.import_module("kdrag.theories.real." + sys.argv[1])
solves = [(thm, elapsed) for tag, thm, elapsed in config.perf_log
          if tag == "solver.check"]
assert solves
durations = [elapsed for _, elapsed in solves]
print(f"Z3 checks: {len(solves)}, total {sum(durations):.4f}s, max {max(durations):.4f}s")
for thm, elapsed in solves:
    assert elapsed < 0.5, ("solver.check", thm, elapsed)
""", module],
        check=True,
    )
