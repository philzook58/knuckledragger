"""Replay the `is_ordinal_succ` step exported at seed 3 (see the issue tracker).

Usage: python zf_succ_unused_hyp_instability.py SEED FILE.smt2
Solves the same parsed query five times with fresh solvers in one process,
with the global smt.random_seed as the kdrag tests set it.
"""

import sys
import time

import z3

z3.set_param("smt.random_seed", int(sys.argv[1]))
fs = z3.parse_smt2_file(sys.argv[2])
results = []
for _ in range(5):
    s = z3.Solver()
    s.set("timeout", 2000)
    s.add(fs)
    t = time.perf_counter()
    r = s.check()
    results.append(f"{r}:{time.perf_counter() - t:.3f}s")
print(sys.argv[2].split("/")[-1], "seed", sys.argv[1], " ".join(results))
