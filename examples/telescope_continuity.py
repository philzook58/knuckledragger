"""Compare scoped proof terms with the continuity PR's existing proofs.

Run with the path to that PR's real/cont.py, which supplies the reference lemmas:
    PYTHONPATH=src python examples/telescope_continuity.py /path/to/real/cont.py

Importing/reference-proof construction is excluded from the measurements.
"""

import cProfile
from functools import partial
from pathlib import Path
import runpy
from statistics import median
import sys
from time import perf_counter

from kdrag import FreshVars, prove as prove_closed
from kdrag.contrib.telescope import Hyp, ScopedProof, Vars, prove, variables
from kdrag.smt import Consts, ForAll, Lambda, RealSort, Reals, Z3Solver
from kdrag.theories.real import RFun, is_cont
from kdrag.utils import alpha_eq


def constant_limit_terms(lemmas):
    a, p, x = Reals("a p x")
    ctx = (Vars((a, p)),)
    local = partial(ScopedProof.from_proof, ctx=ctx)
    constant = Lambda(x, a)
    at_point = local(lemmas["cont_at_of_is_cont"])(
        constant, p, local(lemmas["continuous_const"])(a)
    )
    limit = local(lemmas["has_lim_at_of_cont_at"])(constant, p, at_point)
    return limit.close().closed


def constant_limit_exprs(lemmas):
    a, p = variables("a p", RealSort())
    (x,) = variables("x", RealSort(), ctx=a.ctx)
    constant = a.weaken(x.ctx).lambda_()
    # Scoped arguments import each lemma into the right context automatically.
    lemma = ScopedProof.from_proof
    at_point = lemma(lemmas["cont_at_of_is_cont"])(
        constant, p, lemma(lemmas["continuous_const"])(a)
    )
    limit = lemma(lemmas["has_lim_at_of_cont_at"])(constant, p, at_point)
    return limit.close().closed


def constant_limit_schematic(lemmas):
    a, p = FreshVars("a p", RealSort())
    (x,) = Reals("x")
    constant = Lambda(x, a)
    at_point = lemmas["cont_at_of_is_cont"](constant, p)(lemmas["continuous_const"](a))
    return lemmas["has_lim_at_of_cont_at"](constant, p)(at_point).forall([a, p])


def addition_terms(lemmas):
    f, g = Consts("f g", RFun)
    (p,) = Reals("p")
    outer = (Vars((f, g)), Hyp(is_cont(f)), Hyp(is_cont(g)))
    ctx = outer + (Vars((p,)),)
    local = partial(ScopedProof.from_proof, ctx=ctx)
    hf, hg = prove(is_cont(f), ctx=ctx), prove(is_cont(g), ctx=ctx)
    point_f = local(lemmas["cont_at_of_is_cont"])(f, p, hf)
    point_g = local(lemmas["cont_at_of_is_cont"])(g, p, hg)
    point_sum = local(lemmas["cont_at_add"])(f, g, p, point_f, point_g)
    # Close only p, retaining the function variables and continuity assumptions.
    definition = ScopedProof.from_proof(is_cont.defn, outer)(f + g)
    result = prove(is_cont(f + g), ctx=outer, by=[point_sum.close(), definition])
    return result.close().close().close().closed


def addition_solver(lemmas):
    f, g = Consts("f g", RFun)
    return prove_closed(
        ForAll([f, g], is_cont(f), is_cont(g), is_cont(f + g)),
        by=[is_cont.defn, lemmas["cont_at_add"]],
    )


def measure(fn, lemmas):
    profile = cProfile.Profile()
    start = perf_counter()
    profile.enable()
    result = fn(lemmas)
    profile.disable()
    elapsed = perf_counter() - start
    checks = [e for e in profile.getstats() if e.code is Z3Solver.check.__code__]
    return (
        result,
        elapsed,
        sum(e.callcount for e in checks),
        sum(e.totaltime for e in checks),
    )


if __name__ == "__main__":
    lemmas = runpy.run_path(str(Path(sys.argv[1]).resolve()))
    for name, baseline, scoped in [
        ("constant limit", constant_limit_schematic, constant_limit_terms),
        ("global addition", addition_solver, addition_terms),
    ]:
        choices = [("baseline", baseline), ("scoped", scoped)]
        if name == "constant limit":
            choices.append(("scoped expressions", constant_limit_exprs))
        times = {label: [] for label, _ in choices}
        for repeat in range(3):
            variants = list(choices)
            if repeat % 2:
                variants.reverse()
            proofs = []
            for label, fn in variants:
                pf, elapsed, calls, solver_time = measure(fn, lemmas)
                times[label].append((elapsed, calls, solver_time))
                proofs.append(pf)
            assert all(alpha_eq(proofs[0].thm, p.thm) for p in proofs[1:])
        for label, runs in times.items():
            print(
                f"{name}, {label}: {median(r[0] for r in runs) * 1000:.2f} ms; "
                f"{runs[0][1]} solver checks, "
                f"{median(r[2] for r in runs) * 1000:.2f} ms solver time"
            )
