"""Alpha-renaming sensitivity from the derivative remainder witness conversion.

Run with `same` and `renamed` in separate processes. A fixed 5,000-unit cap
exposes the difference; the original in-process timeout used 1,000 ms alone.
"""

import sys
import time

import z3 as z

R = z.RealSort()
f = z.Array("F", R, R)
p, k, e, d, x, y = z.Reals("p k e d x y")
abs_ = z.Function("abs", R, R)


def witness(v):
    return z.Exists(
        d,
        z.And(
            d > 0,
            z.ForAll(
                v,
                z.Implies(
                    abs_(v - p) < d,
                    abs_(f[v] - f[p] - k * (v - p)) <= e / 2 * abs_(v - p),
                ),
            ),
        ),
    )


s = z.Solver()
s.set(timeout=1000, rlimit=5000)
s.add(z.Implies(e / 2 > 0, witness(x)), e > 0)
s.add(z.Not(witness(y if sys.argv[1] == "renamed" else x)))
start = time.perf_counter()
result = s.check()
print(z.get_version_string(), sys.argv[1], result, s.reason_unknown())
print(f"seconds={time.perf_counter() - start:.4f}")
print(f"rlimit count={s.statistics().get_key_value('rlimit count')}")
