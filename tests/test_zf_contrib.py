import subprocess
import sys

import pytest


@pytest.mark.parametrize(
    "modules,seed",
    [
        ("nat", 0),
        ("fun", 0),
        ("rec", 0),
        ("rec", 1),
        ("fun nat rec", 7),
    ],
)
def test_zf_proofs(modules, seed):
    # Import in a fresh process so the skolemized infinity witness is created once.
    subprocess.run(
        [
            sys.executable,
            "-c",
            """
import importlib
import sys
import kdrag.config as config
import kdrag.smt as smt
smt.set_param("smt.random_seed", int(sys.argv[1]))
import kdrag.theories.zf.zf

config.timing = True
for module in sys.argv[2].split():
    importlib.import_module("kdrag.contrib.zf." + module)
solves = [(thm, elapsed) for tag, thm, elapsed in config.perf_log
          if tag == "solver.check"]
assert solves
for thm, elapsed in solves:
    assert elapsed < 0.5, ("solver.check", thm, elapsed)
""",
            str(seed),
            modules,
        ],
        check=True,
    )


def test_zf_nat_only_axiom_is_infinity():
    import kdrag.contrib.zf.nat as nat

    with open(nat.__file__) as f:
        src = f.read()
    assert src.count("axiom(") == 1
    assert "infinity_ax = axiom(" in src
