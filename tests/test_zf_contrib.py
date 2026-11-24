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
        ("ordinal", 0),
        ("ordinal", 8),
        ("trec", 0),
        ("trec", 9),
        ("sim", 0),
        ("fun nat rec arith order finite card poset ordinal trec sim", 3),
        ("fun nat rec arith order finite card poset ordinal trec sim", 7),
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


def _axioms_used(modules):
    import importlib

    import kdrag as kd

    proofs = [
        v
        for mod in modules
        for v in vars(importlib.import_module("kdrag.contrib.zf." + mod)).values()
        if isinstance(v, kd.kernel.Proof)
    ]
    deps = _dependencies(proofs)
    return {id(p) for p in deps if p.reason == ["axiom"]}, deps


@pytest.mark.parametrize(
    "modules,replacement",
    [
        (
            [
                "nat",
                "fun",
                "rec",
                "arith",
                "order",
                "finite",
                "card",
                "poset",
                "trec",
                "sim",
            ],
            False,
        ),
        (["ordinal"], True),
    ],
)
def test_zf_contrib_axioms(modules, replacement):
    # contrib.zf rests on the theories.zf axioms plus infinity, adding Replacement
    # only where noted, with no Foundation and never the global-choice `pick`.
    import kdrag.theories.zf.zf as zf
    from kdrag.contrib.zf.nat import infinity_ax
    from kdrag.contrib.zf.ordinal import elem_repl

    allowed = [
        zf.ext_ax,
        zf.elem_emp,
        zf.elem_upair,
        zf.elem_sep,
        zf.bigunion_ax,
        zf.elem_pow,
        infinity_ax,
    ]
    if replacement:
        allowed.append(elem_repl)
    used, deps = _axioms_used(modules)
    assert used <= {id(ax) for ax in allowed}
    assert not any(p is zf.elem_pick0 for p in deps)
