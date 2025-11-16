# Knuckledragger

<img src="https://raw.githubusercontent.com/philzook58/knuckledragger/main/docs/logo.webp" alt="drawing" width="200" align="left"/>

Knuckledragger ([git repo](https://github.com/philzook58/knuckledragger)) is an attempt at creating a down to earth, highly automated interactive proof assistant in python. The goal is to support applications like software/hardware verification, calculus, equational reasoning, and numerical bounds.

<br clear="left"/>

## Installation

To install run

```bash
python3 -m pip install git+https://github.com/philzook58/knuckledragger.git
```

Or to install locally

```bash
git clone https://github.com/philzook58/knuckledragger.git
cd knuckledragger
python3 -m pip install -e .
```

## Getting Started

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](https://colab.research.google.com/github/philzook58/knuckledragger/blob/master/examples/short_talk.ipynb) [youtube](https://youtu.be/ENwKBC8dN4M)

```python
import kdrag as kd
import kdrag.smt as smt # smt is literally a reexporting of z3

# Anything Z3 can do on it's own, we can "prove" with no extra work
p,q = smt.Bools("p q")
simple_taut = kd.prove(smt.Implies(p, smt.Or(p, q)))

# The returned objects are `Proof`, not smt.ExprRef` formulas
assert isinstance(simple_taut, kd.Proof)
assert not isinstance(simple_taut, smt.ExprRef)

# kd.prove will throw an error if the theorem is not provable
try:
    false_lemma = kd.prove(smt.Implies(p, smt.And(p, q)), timeout=10)
    print("This will not be reached")
except kd.kernel.LemmaError as e:
    pass

# Z3 also supports things like Reals, Ints, BitVectors and strings
x = smt.Real("x")
real_trich = kd.prove(smt.ForAll([x], smt.Or(x < 0, x == 0, 0 < x)))

x = smt.BitVec("x", 32)
or_idem = kd.prove(smt.ForAll([x], x | x == x))

###################################################################
###################################################################

# But the point of Knuckledragger is really for the things Z3 can't do in one shot

# Knuckledragger support algebraic datatypes and induction
Nat = kd.Inductive("MyNat")
Zero = Nat.declare("Zero")
Succ = Nat.declare("Succ", ("pred", Nat))
Nat = Nat.create()

# We can define an addition function by cases
n,m = smt.Consts("n m", Nat)
add = smt.Function("add", Nat, Nat, Nat)
add = kd.define("add", [n,m], 
    kd.cond(
        (n.is_Zero, m),
        (n.is_Succ, Nat.Succ(add(n.pred, m)))
))

# There is a notation overloading mechanism modelled after python's singledispatch
kd.notation.add.register(Nat, add)

# The definitional lemma is not available to the solver unless you give it
add_zero_x = kd.prove(smt.ForAll([n], Nat.Zero + n == n), by=[add.defn])
add_succ_x = kd.prove(smt.ForAll([n,m], Nat.Succ(n) + m == Nat.Succ(n + m)), by=[add.defn])

# More involved proofs can be more easily done in an interactive tactic
# Under the hood, this boils down to calls to kd.prove
# These proofs are best understood by seeing the interactive output in a Jupyter notebook
l = kd.Lemma(smt.ForAll([n], n + Nat.Zero == n))
# Output: [] ?|= ForAll(n, add(n, Zero) == n)

_n = l.fix()            
# Output: [] ?|= add(n!0, Zero) == n!2213

l.induct(_n)              
# Output: [] ?|= add(Zero, Zero) == Zero

# Base case
l.auto(by=[add.defn])
# Output: [] ?|= ForAll(a!0, Implies(add(a!0, Zero) == a!0, add(Succ(a!0), Zero) == Succ(a!0)))

# Inductive case
l.auto(by=[add.defn])
# Output: Nothing to do!

# Finally the actual Proof is built
add_x_zero = l.qed()

###################################################################
###################################################################

# But we can also build our own sorts and axiomatic theories.
# https://en.wikipedia.org/wiki/Group_(mathematics)
G = smt.DeclareSort("G")
mul = smt.Function("mul", G, G, G)
e = smt.Const("e", G)
inv = smt.Function("inv", G, G)

kd.notation.mul.register(G, mul)

x, y, z = smt.Consts("x y z", G)
mul_assoc = kd.axiom(smt.ForAll([x, y, z], x * (y * z) == (x * y) * z))
id_left = kd.axiom(smt.ForAll([x], e * x == x))
inv_left = kd.axiom(smt.ForAll([x], inv(x) * x == e))

# The Calc tactic can allow one to write explicit equational proofs
c = kd.Calc([x], x * inv(x))
c.eq(e * (x * inv(x)), by=[id_left])
c.eq((inv(inv(x)) * inv(x)) * (x * inv(x)), by=[inv_left])
c.eq(inv(inv(x)) * ((inv(x) * x) * inv(x)), by=[mul_assoc])
c.eq(inv(inv(x)) * (e * inv(x)), by=[inv_left])
c.eq(inv(inv(x)) * inv(x), by=[id_left])
c.eq(e, by=[inv_left])
inv_right = c.qed()
```

For more on using z3py

- <https://ericpony.github.io/z3py-tutorial/guide-examples.htm>
- The z3 guide <https://microsoft.github.io/z3guide/>
- The z3py [documentation](https://z3prover.github.io/api/html/namespacez3py.html)
- <https://github.com/philzook58/z3_tutorial> ([video](https://www.youtube.com/watch?v=56IIrBZy9Rc&feature=youtu.be&ab_channel=BroadInstitute))

For more on interactive theorem proving (This is a lot to take in)

- [Software Foundations](https://softwarefoundations.cis.upenn.edu/) - Coq
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/title_page.html)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Isabelle Tutorial](https://isabelle.in.tum.de/documentation.html)
- [HOL Light Tutorial](https://hol-light.github.io/tutorial.pdf)

A recent summary talk of Knuckledragger was presented at NEPLS 2025

[![Watch the video](https://img.youtube.com/vi/ENwKBC8dN4M/default.jpg)](https://youtu.be/ENwKBC8dN4M)

## Blog Posts

- [ZF style set theory in Knuckledragger I](https://www.philipzucker.com/zf_knuckle1/)
- [Proving the Infinitude of Primes in Knuckledragger](https://www.philipzucker.com/knuckle_primes/)
- [Proof Rules for MetaSMT](https://www.philipzucker.com/kdrag_proof_rules/)
- [A Python CLI for Verifying Assembly](https://www.philipzucker.com/asm_verify3/)
- [Knuckledragger Analysis Etudes](https://www.philipzucker.com/knuckle_analysis1/)
- [Semantic Refinement/Dependent Typing for Knuckledragger/SMTLIB Pt 1](https://www.philipzucker.com/refinement_kdrag1/)
- [Verified Assembly 2: Memory, RISC-V, Cuts for Invariants, and Ghost Code](https://www.philipzucker.com/asm_verify2/)
- [Semi-Automated Assembly Verification in Python using pypcode Semantics](https://www.philipzucker.com/assembly_verify/)
- [NEPLS 2025 and a Short Talk on Knuckledragger](https://www.philipzucker.com/nepls_2025/) [video](https://www.youtube.com/watch?v=ENwKBC8dN4M&ab_channel=PhilipZucker)
- ["Verified" "Compilation" of "Python" with Knuckledragger, GCC, and Ghidra](https://www.philipzucker.com/knuckle_C_pcode/)
- [A Small Prolog on the Z3 AST](https://www.philipzucker.com/knuck_prolog/)
- [Shallow Embedding Logics in Z3 pt. I](https://www.philipzucker.com/shallow_logic_knuckle/)
- [Knuth Bendix Solver on Z3 AST](https://www.philipzucker.com/knuth_bendix_knuck/)
- [Generics and Typeclasses in Knuckledragger](https://www.philipzucker.com/knuckle_typeclass/)
- [More Knuckledragger: Simp, Inductive Relations, Sympy NbE, and Software Foundations](https://www.philipzucker.com/knuckle_update_nbe/)
- [Translating Cody's Lean Sheffer Stroke Proof to Knuckledragger with ChatGPT](https://www.philipzucker.com/cody_sheffer/)
- ['Lean-style' Tactics in Knuckledragger](https://www.philipzucker.com/knuckle_lemma/)
- [State of Knuckledragger, a Semi-Automated Python Proof Assistant](https://www.philipzucker.com/state_o_knuck/)
- [Proving Sum n = n*(n-1)/2 and that 1/n tends to 0](https://www.philipzucker.com/analysis_knuckle/)
- [Peano Nats in Interactive SMT](https://www.philipzucker.com/sqrt2_2/)
- [Experiments in the Irrationality of Sqrt 2 with SMT](https://www.philipzucker.com/sqrt2/)
- [Knuckledragger Update: ATP for Python Interactive Theorem Proving](https://www.philipzucker.com/knuckledrag2/)
- [Knuckledragger: Experimenting with a Python Proof Assistant](https://www.philipzucker.com/python-itp/)

## Comparison to Other Systems

- [Z3](https://github.com/Z3Prover/z3): Knuckledragger has a superset of the capabilities of Z3 since it is built on top of it. Enables rigorous chaining of Z3 calls. Better facilities for higher order and quantifier reasoning.
- [sympy](https://www.sympy.org/) and sage: More manual manipulation is to be expected, but also more logically sound. Everything is integrated in a cohesive fabric of first order logic.
- Lean and Coq: No dependent types, larger trusted code base, a higher baseline of automation.
- [Isabelle](https://isabelle.in.tum.de/) and [HOLpy](https://gitee.com/bhzhan/holpy): Knuckledragger is similar in many respects to the systems. It has a lack of parametric types and weaker higher order reasoning. Knuckledragger is a library, not a framework. Heavy reuse of already existing python things is preferred whenever possible (Jupyter, z3py, sympy, python idioms). It is seamlessly integrated with z3py.

## Design

It is not desirable or within my capabilities to build a giant universe in which to live. The goal is to take a subtle blade and bolt together things that already exist.

Using widespread and commonly supported languages gives a huge leg up in terms of tooling and audience. Python is the modern lingua franca of computing. It has a first class interactive experience and extensive bindings to projects in other languages.

Core functionality comes from [Z3](https://github.com/Z3Prover/z3). The Z3 python api is a de facto standard. The term and formula data structures of knuckledragger are literally z3 python terms and formula. To some degree, Knuckledragger is a metalayer to guide smt through proofs it could perhaps do on its own, but it would get lost.

A hope is to be able to use easy access to [Jupyter](https://jupyter.org/), [copilot](https://copilot.microsoft.com/), ML ecosystems, [sympy](https://www.sympy.org/), [cvxpy](https://www.cvxpy.org/), [numpy](https://numpy.org/), [scipy](https://scipy.org/), [egglog](https://egglog-python.readthedocs.io/latest/), [Julia](https://github.com/JuliaPy/PythonCall.jl), [Prolog](https://www.swi-prolog.org/pldoc/man?section=janus-call-prolog), [Maude](https://fadoss.github.io/maude-bindings/), [calcium](https://fredrikj.net/calcium/), [flint](https://fredrikj.net/python-flint/), [Mathematica](https://reference.wolfram.com/language/WolframClientForPython/), and [sage](https://www.sagemath.org/) will make metaprogramming in this system very powerful. I maintain the option to just trust these results but hopefully they can be translated into arguments the kernel can understand.

The core logic is more or less multi-sorted first order logic aka [SMT-LIB2](https://smt-lib.org/).

Big features that ATPs do not often support are induction, definitions, and other axiom schema. Knuckledragger supports these.

Other theorem provers of interest: [cvc5](https://cvc5.github.io/), [Vampire](https://vprover.github.io/), [eprover](https://wwwlehre.dhbw-stuttgart.de/~sschulz/E/E.html), [Twee](https://nick8325.github.io/twee/), [nanoCoP](https://leancop.de/nanocop/).

The de Bruijn criterion is going to be bent or broken in certain senses. Attention is paid to what is kernel and what is not. Proof objects are basically trees recording chains of lemmas discharged by Automated Theorem Prover (ATP) calls. Soundness will be attempted, accidental misuse will be made difficult but not impossible.

Isabelle and ACL2 are the strongest influences. If you want dependent type theory, you are at a level of investment and sophistication that it behooves you to be in another system. Should there be a strong automated DTT solver someday, I will reconsider.

## FAQ

- Is this for proving about properties about python programs?
  - Not directly. Proving properties of general python programs in a highly assured manner is extremely difficult due to its extreme dynamic nature. There are a couple caveats to this answer.
    1. Knuckledragger does enable you to model your algorithms and extract/interpret them to python.
    2. A subset of purely-function, strongly-typed python can be reflected directly into the Knuckledragger logic.
    3. Domain specific modelling of important python ecosystem libraries is a WIP.
- Is Knuckledragger python specific?
  - Python is a useful and important platform, but the core of the design can be ported to many languages. The design is based around the chaining of calls to z3 which gets you a lot of distance for free.
    - [SBV](https://hackage.haskell.org/package/sbv-11.0/docs/Data-SBV-Tools-KnuckleDragger.html) - Haskell
    - Yours here!

## License & Citation

MIT licensed. See LICENSE for more information.

Citing this repository is highly appreciated but not required by the license.

```
@software{knuckledragger2025,
  author = {Philip Zucker},
  title = {{Knuckledragger: A Low Barrier Proof Assistant}},
  url = {https://github.com/philzook58/knuckledragger},
  month = {1},
  year = {2025}
}
```
