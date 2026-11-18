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


def test_lim_lemma_composes_limit_rules():
    import kdrag.theories.real.seq as seq
    from kdrag.theories.real.lim_algebra import lim_lemma

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
    import kdrag.theories.real.seq as seq
    from kdrag.theories.real.lim_algebra import lim_lemma

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
