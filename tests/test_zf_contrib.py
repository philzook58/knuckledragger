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
        ("arith", 0),
        ("arith", 3),
        ("order", 0),
        ("order", 5),
        ("finite", 0),
        ("finite", 2),
        ("card", 0),
        ("card", 4),
        ("poset", 0),
        ("poset", 6),
        ("fun nat rec arith order finite card poset", 7),
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


def _dependencies(proofs):
    import kdrag as kd

    todo, seen, out = list(proofs), set(), []
    while todo:
        p = todo.pop()
        if isinstance(p, (list, tuple)):
            todo.extend(p)
        elif isinstance(p, kd.kernel.Proof) and id(p) not in seen:
            seen.add(id(p))
            out.append(p)
            todo.extend(p.reason)
    return out


def test_zf_contrib_axioms():
    # contrib.zf should rest on ZF minus Replacement and Foundation, without choice:
    # the theories.zf axioms plus infinity, and never the global-choice `pick`.
    import importlib

    import kdrag as kd
    import kdrag.theories.zf.zf as zf

    modules = ["nat", "fun", "rec", "arith", "order", "finite", "card", "poset"]
    proofs = [
        v
        for mod in modules
        for v in vars(importlib.import_module("kdrag.contrib.zf." + mod)).values()
        if isinstance(v, kd.kernel.Proof)
    ]
    deps = _dependencies(proofs)
    from kdrag.contrib.zf.nat import infinity_ax

    allowed = {
        id(ax)
        for ax in [
            zf.ext_ax,
            zf.elem_emp,
            zf.elem_upair,
            zf.elem_sep,
            zf.bigunion_ax,
            zf.elem_pow,
            infinity_ax,
        ]
    }
    used = [p for p in deps if p.reason == ["axiom"]]
    assert {id(p) for p in used} <= allowed, [
        p.thm for p in used if id(p) not in allowed
    ]
    assert not any(p is zf.elem_pick0 for p in deps)
