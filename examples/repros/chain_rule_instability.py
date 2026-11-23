"""Reduced query from PR #93's macOS chain-rule timeout (Z3 only).

Run each case in a fresh process; results depend on the Z3 version:
    python examples/repros/chain_rule_instability.py 0
    python examples/repros/chain_rule_instability.py 7
    python examples/repros/chain_rule_instability.py 0 instantiated

The 70,000-unit resource cap exposes seed sensitivity on Linux. It is not the
original macOS timeout, which used 1,000 ms without this resource cap.
"""

import sys
import time

import z3 as z

R = z.RealSort()
A = z.ArraySort(R, R)
f, g, F, G = z.Consts("f g F G", A)
p, a, b, x = z.Reals("p a b x")
mul = z.Function("mul", A, A, A)
lim = z.Function("lim", A, R, R, z.BoolSort())


def quot(f, p):
    return z.Lambda(x, (f[x] - f[p]) / (x - p))


def slope(f, p, a):
    return z.Store(quot(f, p), p, a)


# Keep this intermediate AST: inlining it changes solver search as well.
composite = z.Lambda(x, g[f[x]])
left = z.Lambda(x, slope(g, f[p], b)[f[x]])
right = slope(f, p, a)
product = mul(left, right)
target = quot(composite, p)
pointwise = z.ForAll(x, z.Implies(x != p, product[x] == target[x]))
# Only the relevant instances of limit congruence and the two algebraic lemmas.
congr = z.Implies(pointwise, z.Implies(lim(product, p, b * a), lim(target, p, b * a)))
mult = z.ForAll([F, G], mul(F, G) == z.Lambda(x, F[x] * G[x]), patterns=[mul(F, G)])
chain = z.ForAll(
    [f, g, p, a, b, x],
    z.Implies(
        x != p,
        quot(z.Lambda(x, g[f[x]]), p)[x] == slope(g, f[p], b)[f[x]] * slope(f, p, a)[x],
    ),
)
if "instantiated" in sys.argv[2:]:
    mult = z.substitute_vars(mult.body(), right, left)
    chain = z.ForAll(x, z.substitute_vars(chain.body(), x, b, a, p, g, f))

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
s = z.Solver()
s.set(timeout=1000, rlimit=70000, random_seed=seed)
s.add(congr, mult, chain, lim(product, p, b * a), z.Not(lim(target, p, b * a)))
start = time.perf_counter()
result = s.check()
print(f"Z3 {z.get_version_string()}, seed={seed}: {result}")
print(f"seconds={time.perf_counter() - start:.4f}; reason={s.reason_unknown()!r}")
print(f"rlimit count={s.statistics().get_key_value('rlimit count')}")
