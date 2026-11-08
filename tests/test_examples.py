import pytest

import runpy
import subprocess
import tempfile


def test_real_analysis():
    import kdrag.config as config
    import kdrag.theories.real  # Load the theory before measuring the examples.

    was_timing = config.timing
    start = len(config.perf_log)
    try:
        config.timing = True
        runpy.run_path("examples/real_analysis.py")
        timings = config.perf_log[start:]
    finally:
        config.timing = was_timing
        del config.perf_log[start:]

    solves = [elapsed for tag, _, elapsed in timings if tag == "solver.check"]
    assert solves
    print(f"Z3 checks: {len(solves)}, total {sum(solves):.4f}s, max {max(solves):.4f}s")
    for tag, thm, elapsed in timings:
        assert elapsed < 0.5, (tag, thm, elapsed)


@pytest.mark.slow
def test_examples():
    import examples.soft_found.lf.indprop
    import examples.soft_found.lf.imp as imp
    #import examples.kt as ks
    imp.AExp
