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


@pytest.mark.parametrize(
    "modules,seed",
    [
        ("kdrag.theories.real.cont", 0),
        ("kdrag.contrib.analysis.cont", 0),
        ("kdrag.theories.real.rseq", 0),
        ("deriv", 0),
        ("integral", 0),
        ("cont deriv rseq finsum integral ftc", 0),
        ("ftc integral finsum rseq deriv cont", 1),
        ("rseq integral cont finsum deriv ftc", 7),
        ("sine", 0),
    ],
)
def test_analysis_proofs(modules, seed):
    # Import in a fresh process: re-executing rseq would redefine its chosen lim.
    subprocess.run(
        [sys.executable, "-c", """
import importlib
import sys
import kdrag.config as config
import kdrag.smt as smt
smt.set_param("smt.random_seed", int(sys.argv[2]))
import kdrag.theories.real
import kdrag.theories.int

config.timing = True
for module in sys.argv[1].split():
    importlib.import_module(module if "." in module else "kdrag.contrib.analysis." + module)
solves = [(thm, elapsed) for tag, thm, elapsed in config.perf_log
          if tag == "solver.check"]
assert solves
durations = [elapsed for _, elapsed in solves]
print(f"Z3 checks: {len(solves)}, total {sum(durations):.4f}s, max {max(durations):.4f}s")
for thm, elapsed in solves:
    assert elapsed < 0.5, ("solver.check", thm, elapsed)
""", modules, str(seed)],
        check=True,
    )


def test_lim_lemma_composes_limit_rules():
    import kdrag.theories.real.rseq as seq
    from kdrag.contrib.analysis.rseq import lim_lemma

    a, b, c = smt.Consts("lim_a lim_b lim_c", real.RSeq)
    e = a * b + seq.smul(2, a)
    # Leaves get limits in order of first occurrence.
    pf = lim_lemma(e)(smt.RealVal(1), smt.RealVal(2))
    kd.prove(
        smt.Implies(smt.And(seq.has_lim(a, 1), seq.has_lim(b, 2)), seq.has_lim(e, 4)),
        by=[pf],
    )
    # Side conditions of the rules become premises.
    quot = lim_lemma(a / (c + seq.const(1)))
    assert "!= 0" in str(quot.thm)


def test_lim_lemma_on_real_terms_in_index():
    import kdrag.theories.real.rseq as seq
    from kdrag.contrib.analysis.rseq import lim_lemma

    a = smt.Const("lim_a", real.RSeq)
    n = smt.Int("lim_n")
    e = 1 + 2 * a[n] / (1 + 3 * a[n] - 4 * a[n] ** 2)
    pf = lim_lemma(e, n)(smt.RealVal(0))
    kd.prove(
        smt.Implies(seq.has_lim(a, 0), seq.has_lim(smt.Lambda([n], e), 1)), by=[pf]
    )
    # 1/n has a known limit, so only a needs a premise.
    inv = lim_lemma(a[n] + smt.RealVal(1) / n, n)
    assert inv.thm.num_vars() == 1
    # Unrecognized terms in n, such as a shifted sequence, are atoms.
    shifted = lim_lemma(a[n + 1] - a[n], n)
    assert "Lambda" in str(shifted.thm.body().arg(0))
