"""Unsat in milliseconds for most seeds, but with the global smt.random_seed = 0
the first check returns unknown (timeout). Usage: python mini.py [seed] [timeout_ms]"""
import sys
import time

import z3

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
timeout = int(sys.argv[2]) if len(sys.argv) > 2 else 1000
z3.set_param("smt.random_seed", seed)

S = z3.DeclareSort("S")
mem = z3.Function("mem", S, S, z3.BoolSort())
le = z3.Function("le", S, S, z3.BoolSort())
RelS = z3.ArraySort(S, S, z3.BoolSort())
is_least = z3.Function("is_least", RelS, S, S, z3.BoolSort())
E = z3.Const("E", S)
k, m, a, x = z3.Consts("k m a x", S)
R = z3.Const("R", RelS)
y = z3.Const("y", S)

facts = [
    # E has an element k below every element of E ...
    z3.Exists([k], z3.And(mem(k, E), z3.ForAll([m], z3.Implies(mem(m, E), le(k, m))))),
    # ... which is what is_least(R, E, k) means for R = le.
    z3.ForAll(
        [R, E, a],
        is_least(R, E, a) == z3.And(mem(a, E), z3.ForAll([x], z3.Implies(mem(x, E), R[a, x]))),
        patterns=[is_least(R, E, a)],
    ),
    z3.Not(z3.Exists([a], is_least(z3.Lambda([x, y], le(x, y)), E, a))),
]

for i in range(20):
    s = z3.Solver()
    s.set("timeout", timeout)
    s.add(*facts)
    t0 = time.perf_counter()
    r = s.check()
    dt = time.perf_counter() - t0
    if r != z3.unsat:
        print(f"solve {i}: {r} ({s.reason_unknown()}) after {dt:.2f}s")
        break
else:
    print("all 20 solves unsat")
print("z3", z3.get_version_string(), "seed", seed)
