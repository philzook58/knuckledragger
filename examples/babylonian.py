"""
Babylonian Method for Square Root - Proof that the sequence is Cauchy

The Babylonian method (also known as Heron's method) is an iterative algorithm
for computing square roots. Given a target number a > 0 and an initial guess x0 > 0,
it produces a sequence:
    x_{n+1} = (x_n + a/x_n) / 2

This file proves properties of this sequence leading towards showing it is Cauchy.
"""

import kdrag as kd
import kdrag.smt as smt
import kdrag.theories.real as real
import kdrag.theories.real.seq as seq

# Basic real variables  
x, y, z, a, eps = smt.Reals("x y z a eps")
n, m, k, N = smt.Ints("n m k N")

# Real sequence type
RSeq = real.RSeq

# Define the Babylonian step function: f(x) = (x + a/x) / 2
# We define this as a simple recursive function
babylonian_seq = smt.Function("babylonian_seq", smt.RealSort(), smt.RealSort(), smt.IntSort(), smt.RealSort())
babylonian_seq = kd.define(
    "babylonian_seq",
    [a, x, n],
    smt.If(n <= 0,
        x,
        (babylonian_seq(a, x, n - 1) + a / babylonian_seq(a, x, n - 1)) / 2
    )
)

# Basic properties of the step function
@kd.Theorem("forall (a x : Real), a > 0 -> x > 0 -> (x + a/x)/2 > 0")
def step_positive(pf):
    """The Babylonian step preserves positivity"""
    a, x = pf.fixes()
    pf.intros()
    pf.intros()
    pf.auto()

# Prove the AM-GM inequality for two positive numbers: (x + y)/2 >= sqrt(xy)
@kd.Theorem("forall (x y : Real), x > 0 -> y > 0 -> (x + y)/2 >= sqrt (x * y)")
def am_gm(pf):
    """Arithmetic mean >= Geometric mean"""
    x, y = pf.fixes()
    pf.intros()
    pf.intros()
    # (x + y)/2 >= sqrt(xy) iff (x + y)^2 >= 4xy iff x^2 + 2xy + y^2 >= 4xy
    # iff x^2 - 2xy + y^2 >= 0 iff (x - y)^2 >= 0
    pf.auto(by=[real.sqrt.defn, real.sqr.defn])

@kd.Theorem("forall (a x : Real), a > 0 -> x > 0 -> (x + a/x)/2 >= sqrt a")
def step_lower_bound(pf):
    """The Babylonian step produces a value >= sqrt(a)"""
    a, x = pf.fixes()
    pf.intros()
    pf.intros()
    # Apply AM-GM with x and a/x
    # (x + a/x)/2 >= sqrt(x * (a/x)) = sqrt(a)
    pf.auto(by=[am_gm, real.sqrt.defn], timeout=2000)

# Prove that all terms in the sequence are positive
@kd.Theorem("forall (a x0 : Real) (n : Int), a > 0 -> x0 > 0 -> n >= 0 -> babylonian_seq a x0 n > 0")
def seq_positive(pf):
    """All terms in the sequence are positive"""
    a, x0, n = pf.fixes()
    pf.intros()
    pf.intros()
    pf.intros()
    
    # Induct on n
    pf.induct(n)
    
    # Case n < 0: contradicts n >= 0
    pf.auto(by=[babylonian_seq.defn])
    
    # Case n == 0: babylonian_seq a x0 0 = x0 > 0
    pf.auto(by=[babylonian_seq.defn])
    
    # Case n > 0: Use IH and step_positive
    _n = pf.fix()
    pf.intros()
    pf.intros()
    pf.auto(by=[babylonian_seq.defn, step_positive], timeout=2000)

# After the first iteration, all terms are bounded below by sqrt(a)
@kd.Theorem("forall (a x0 : Real) (n : Int), a > 0 -> x0 > 0 -> n >= 1 -> babylonian_seq a x0 n >= sqrt a")
def seq_lower_bound(pf):
    """After the first step, all terms are >= sqrt(a)"""
    a, x0, n = pf.fixes()
    pf.intros()
    pf.intros()
    pf.intros()
    
    # Induct on n >= 1
    pf.induct(n)
    
    # Case n < 1: contradicts n >= 1
    pf.auto()
    
    # Case n == 1: babylonian_seq a x0 1 = (x0 + a/x0)/2 >= sqrt(a)
    pf.auto(by=[babylonian_seq.defn, step_lower_bound], timeout=2000)
    
    # Case n > 1: Use IH and step_lower_bound
    _n = pf.fix()
    pf.intros()
    pf.intros()
    pf.auto(by=[babylonian_seq.defn, step_lower_bound, seq_positive], timeout=2000)

# The sequence is decreasing after the first term
@kd.Theorem("forall (a x0 : Real) (n : Int), a > 0 -> x0 >= sqrt a -> n >= 0 -> babylonian_seq a x0 (n+1) <= babylonian_seq a x0 n")
def seq_decreasing_from_above(pf):
    """If x0 >= sqrt(a), the sequence is decreasing"""
    a, x0, n = pf.fixes()
    pf.intros()
    pf.intros()
    pf.intros()
    
    # When x >= sqrt(a), the step (x + a/x)/2 <= x
    # This follows from: x + a/x <= 2x iff a/x <= x iff a <= x^2 iff sqrt(a) <= x
    pf.induct(n)
    
    # Case n < 0
    pf.auto(by=[babylonian_seq.defn])
    
    # Case n == 0
    pf.auto(by=[babylonian_seq.defn, step_lower_bound], timeout=2000)
    
    # Case n > 0
    _n = pf.fix()
    pf.intros()
    pf.intros()
    pf.auto(by=[babylonian_seq.defn, seq_lower_bound, seq_positive], timeout=2000)

# Statement of Cauchy property (without full proof)
# This is the main theorem we're working towards
is_cauchy_babylonian = kd.axiom(
    kd.QForAll(
        [a, x],
        a > 0,
        x > 0,
        seq.is_cauchy(smt.Lambda([n], babylonian_seq(a, x, n)))
    )
)

print("=" * 60)
print("Babylonian Method - Cauchy Sequence Proof")
print("=" * 60)
print()
print("Proved theorems:")
print(f"  1. Step preserves positivity: {step_positive.thm}")
print(f"  2. AM-GM inequality: {am_gm.thm}")  
print(f"  3. Step lower bound: {step_lower_bound.thm}")
print(f"  4. Sequence stays positive: {seq_positive.thm}")
print(f"  5. Sequence bounded below: {seq_lower_bound.thm}")
print(f"  6. Sequence decreasing: {seq_decreasing_from_above.thm}")
print()
print("Main theorem (stated as axiom):")
print(f"  The Babylonian sequence is Cauchy")
print()
print("The key properties are established:")
print("  - The sequence is bounded below by sqrt(a)")
print("  - The sequence is monotonically decreasing (when x0 >= sqrt(a))")
print("  - Every term is positive")
print("These properties together imply the sequence is Cauchy by the")
print("monotone convergence theorem.")
