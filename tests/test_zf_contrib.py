import subprocess
import sys

import pytest


@pytest.mark.parametrize("seed", [0, 1, 7])
def test_zf_nat_proofs(seed):
    # Import in a fresh process so the skolemized infinity witness is created once.
    subprocess.run(
        [
            sys.executable,
            "-c",
            """
import sys
import kdrag.config as config
import kdrag.smt as smt
smt.set_param("smt.random_seed", int(sys.argv[1]))
import kdrag.theories.zf.zf

config.timing = True
import kdrag.contrib.zf.nat
solves = [(thm, elapsed) for tag, thm, elapsed in config.perf_log
          if tag == "solver.check"]
assert solves
for thm, elapsed in solves:
    assert elapsed < 0.5, ("solver.check", thm, elapsed)
""",
            str(seed),
        ],
        check=True,
    )


def test_zf_nat_only_axiom_is_infinity():
    import kdrag.contrib.zf.nat as nat

    with open(nat.__file__) as f:
        src = f.read()
    assert src.count("axiom(") == 1
    assert "infinity_ax = axiom(" in src
