import subprocess
import sys

import pytest


@pytest.mark.parametrize(
    "modules,seed",
    [
        ("nat", 0),
        ("fun", 0),
        ("dsum", 0),
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
        ("ordset", 0),
        ("ordset", 4),
        ("count", 0),
        ("count", 2),
        ("oarith", 0),
        ("oarith", 4),
        ("omul", 0),
        ("omul", 6),
        ("osub", 0),
        ("osub", 9),
        ("orec", 0),
        ("orec", 13),
        ("opow", 0),
        ("opow", 6),
        ("choice", 0),
        ("zorn", 0),
        ("zorn", 5),
        ("wellord", 0),
        ("wellord", 9),
        ("countable", 0),
        ("countable", 7),
        ("cardarith", 0),
        ("cardarith", 6),
        ("cardinal", 0),
        ("cardinal", 11),
        ("cls", 0),
        ("cls", 9),
        ("nat_int", 0),
        ("nat_int", 3),
        (
            "fun nat dsum rec arith order finite card poset ordinal trec sim ordset count oarith omul osub orec opow choice zorn wellord countable cardarith cardinal cls nat_int",
            3,
        ),
        (
            "fun nat dsum rec arith order finite card poset ordinal trec sim ordset count oarith omul osub orec opow choice zorn wellord countable cardarith cardinal cls nat_int",
            7,
        ),
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
    "modules,extra",
    [
        (
            [
                "nat",
                "fun",
                "dsum",
                "rec",
                "arith",
                "order",
                "finite",
                "card",
                "poset",
                "trec",
                "sim",
            ],
            "none",
        ),
        (
            [
                "ordinal",
                "ordset",
                "count",
                "oarith",
                "omul",
                "osub",
                "orec",
                "opow",
                "countable",
                "cardarith",
                "cls",
            ],
            "replacement",
        ),
        (["choice", "zorn", "wellord", "cardinal"], "choice"),
        (["nat_int"], "int"),
    ],
)
def test_zf_contrib_axioms(modules, extra):
    # contrib.zf rests on the theories.zf axioms plus infinity, adding Replacement
    # and definite description, or Halmos' axiom of choice, only where noted, with
    # no Foundation and never the global-choice `pick`.
    import kdrag.theories.zf.zf as zf
    from kdrag.contrib.zf.nat import infinity_ax
    from kdrag.contrib.zf.choice import choice_ax
    from kdrag.contrib.zf.ordinal import elem_repl, the_eq

    allowed = [
        zf.ext_ax,
        zf.elem_emp,
        zf.elem_upair,
        zf.elem_sep,
        zf.bigunion_ax,
        zf.elem_pow,
        infinity_ax,
    ]
    if extra == "replacement":
        allowed += [elem_repl, the_eq]
    if extra == "choice":
        allowed += [elem_repl, the_eq, choice_ax]
    if extra == "int":
        # Only the Int induction axiom behind theories.int.induct_nat_ax.
        import kdrag.theories.int as int_

        allowed += [
            p for p in _dependencies([int_.induct_nat_ax]) if p.reason == ["axiom"]
        ]
    used, deps = _axioms_used(modules)
    assert used <= {id(ax) for ax in allowed}
    assert not any(p is zf.elem_pick0 for p in deps)
