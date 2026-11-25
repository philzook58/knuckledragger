import subprocess
import sys

import pytest


@pytest.mark.parametrize("seed", [0, 1, 7])
def test_linalg_proofs(seed):
    # Fresh process per seed so every proof is rechecked under that seed.
    subprocess.run(
        [sys.executable, "-c", """
import sys
import kdrag.config as config
import kdrag.smt as smt
smt.set_param("smt.random_seed", int(sys.argv[1]))
import kdrag.theories.int
import kdrag.theories.real.rseq

config.timing = True
import kdrag.contrib.linalg.dim
solves = [(thm, elapsed) for tag, thm, elapsed in config.perf_log
          if tag == "solver.check"]
assert solves
durations = [elapsed for _, elapsed in solves]
print(f"Z3 checks: {len(solves)}, total {sum(durations):.4f}s, max {max(durations):.4f}s")
for thm, elapsed in solves:
    assert elapsed < 0.5, ("solver.check", thm, elapsed)
""", str(seed)],
        check=True,
    )
