"""Import the real theories with timings, prove a lemma, and check timeouts fire.

Runs identically under CPython and Pyodide (see tools/pyodide_smoke.mjs).
"""

import importlib
import time

MODULES = [
    "kdrag",
    "kdrag.theories.real",
    "kdrag.theories.real.rseq",
    "kdrag.theories.real.rset",
    "kdrag.theories.real.cont",
    "kdrag.theories.real.analysis",
]

start = time.perf_counter()
for name in MODULES:
    t = time.perf_counter()
    importlib.import_module(name)
    print(f"import {name}: {time.perf_counter() - t:.2f}s")
print(f"all imports: {time.perf_counter() - start:.2f}s")

import kdrag as kd  # noqa: E402
import kdrag.smt as smt  # noqa: E402
import kdrag.theories.real as real  # noqa: E402

x, y = smt.Reals("x y")
t = time.perf_counter()
pf = kd.prove(
    smt.ForAll([x, y], real.sqr(x + y) <= 2 * (real.sqr(x) + real.sqr(y))),
    by=[real.sqr.defn],
)
print(f"{pf}: {time.perf_counter() - t:.2f}s")

# An E-matching loop is the typical failing proof; the timeout must fire, not hang.
# (Under Pyodide, z3 5.3.3.0 timeouts never fire on nonlinear integer goals.)
n = smt.Int("n")
f = smt.Function("f", smt.IntSort(), smt.IntSort())
g = smt.Function("g", smt.IntSort(), smt.IntSort())
loop = smt.ForAll([n], f(n) == f(g(n)) + 1, patterns=[f(n)])
t = time.perf_counter()
try:
    kd.prove(smt.Implies(loop, f(0) != 0), timeout=1000)
    raise AssertionError("unexpectedly proved")
except (TimeoutError, kd.kernel.LemmaError) as e:
    print(f"failed as expected: {type(e).__name__}")
elapsed = time.perf_counter() - t
print(f"timeout=1000 returned after {elapsed:.2f}s")
assert elapsed < 10, "timeout did not fire"
print("OK")
