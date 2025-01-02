# Knuckledragger

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](http://colab.research.google.com/github/philzook58/knuckledragger/blob/main/tutorial.ipynb)

<img src="https://raw.githubusercontent.com/philzook58/knuckledragger/main/logo.webp" alt="drawing" width="200" align="left"/>

Knuckledragger is an attempt at creating a down to earth, highly automated interactive proof assistant in python. It is not attempting to be the most interesting, expressive, or flexible logic in the world. The goal is to support applications like software/hardware verification, calculus, equational reasoning, and numerical bounds.

<br clear="left"/>

## Installation

```bash
python3 -m pip install git+https://github.com/philzook58/knuckledragger.git
python3 -m kdrag.solvers install # install extra solvers
```

Or to install locally

```bash
git clone https://github.com/philzook58/knuckledragger.git
cd knuckledragger
python3 -m pip install -e .
./install.sh # install extra solvers
```

## Getting Started

```python
import kdrag as kd
import kdrag.smt as smt # smt is literally a reexporting of z3

# Anything Z3 can do on it's own, we can "prove" with no extra work
p,q = smt.Bools("p q")
simple_taut = kd.lemma(smt.Implies(p, smt.Or(p, q)))

# The returned objects are `Proof`, not smt.ExprRef` formulas
assert kd.kernel.is_proof(simple_taut)
assert not isinstance(simple_taut, smt.ExprRef)

# kd.lemma will throw an error if the theorem is not provable
try:
    false_lemma = kd.lemma(smt.Implies(p, smt.And(p, q)))
    assert False # This will not be reached
except kd.kernel.LemmaError as e:
    pass

# Z3 also supports things like Reals, Ints, BitVectors and strings
x = smt.Real("x")
real_trich = kd.lemma(smt.ForAll([x], smt.Or(x < 0, x == 0, 0 < x)))

x = smt.BitVec("x", 32)
or_idem = kd.lemma(smt.ForAll([x], x | x == x))

###################################################################
###################################################################

# But the point of Knuckledragger is really for the things Z3 can't do in one shot

# Knuckledragger support algebraic datatypes and induction
Nat = kd.Inductive("Nat", strict=False)
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
add_zero_x = kd.lemma(smt.ForAll([n], Nat.Zero + n == n), by=[add.defn])
add_succ_x = kd.lemma(smt.ForAll([n,m], Nat.Succ(n) + m == Nat.Succ(n + m)), by=[add.defn])

# More involved proofs can be more easily done in an interactive tactic
# Under the hood, this boils down to calls to kd.lemma
# These proofs are best understood by seeing the interactive output in a Jupyter notebook
l = kd.Lemma(smt.ForAll([n], n + Nat.Zero == n))

# [] ?|- ForAll(n, add(n, Zero) == n)
_n = l.fixes()            

# [] ?|- add(n!0, Zero) == n!2213
l.induct(_n)              

# Case n!0 == Nat.Zero
# [] ?|- add(Zero, Zero) == Zero
l.auto(by=[add.defn])

# Case n!0 == Nat.Succ(n.pred)
# [] ?|- ForAll(a!0, Implies(add(a!0, Zero) == a!0, add(Succ(a!0), Zero) == Succ(a!0)))
l.auto(by=[add.defn])

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

## Blog Posts

- [Translating Cody's Lean Sheffer Stroke Proof to Knuckledragger with ChatGPT](https://www.philipzucker.com/cody_sheffer/)
- ['Lean-style' Tactics in Knuckledragger](https://www.philipzucker.com/knuckle_lemma/)
- [State of Knuckledragger, a Semi-Automated Python Proof Assistant](https://www.philipzucker.com/state_o_knuck/)
- [Proving Sum n = n*(n-1)/2 and that 1/n tends to 0](https://www.philipzucker.com/analysis_knuckle/)
- [Peano Nats in Interactive SMT](https://www.philipzucker.com/sqrt2_2/)
- [Experiments in the Irrationality of Sqrt 2 with SMT](https://www.philipzucker.com/sqrt2/)
- [Knuckledragger Update: ATP for Python Interactive Theorem Proving](https://www.philipzucker.com/knuckledrag2/)
- [Knuckledragger: Experimenting with a Python Proof Assistant](https://www.philipzucker.com/python-itp/)

## Knuckledragger isn't Python

The design is based around the chaining of calls to z3. Python is a useful platform, but the core of the design can be ported to many languages.

- [SBV](https://hackage.haskell.org/package/sbv-11.0/docs/Data-SBV-Tools-KnuckleDragger.html) - Haskell
- Yours here!

## Design

It is not desirable or within my capabilities to build a giant universe in which to live. The goal is to take a subtle blade and bolt together things that already exist.

Using widespread and commonly supported languages gives a huge leg up in terms of tooling and audience. Python is the modern lingua franca of computing. It has a first class interactive experience and extensive bindings to projects in other languages.

Core functionality comes from [Z3](https://github.com/Z3Prover/z3). The Z3 python api is a de facto standard. The term and formula data structures of knuckledragger are literally z3 python terms and formula. To some degree, knuckledragger is a metalayer to guide smt through proofs it could perhaps do on its own, but it would get lost.

A hope is to be able to use easy access to [Jupyter](https://jupyter.org/), [copilot](https://copilot.microsoft.com/), ML ecosystems, [sympy](https://www.sympy.org/), [cvxpy](https://www.cvxpy.org/), [numpy](https://numpy.org/), [scipy](https://scipy.org/), [egglog](https://egglog-python.readthedocs.io/latest/), [Julia](https://github.com/JuliaPy/PythonCall.jl), [Prolog](https://www.swi-prolog.org/pldoc/man?section=janus-call-prolog), [Maude](https://fadoss.github.io/maude-bindings/), [calcium](https://fredrikj.net/calcium/), [flint](https://fredrikj.net/python-flint/), [Mathematica](https://reference.wolfram.com/language/WolframClientForPython/), and [sage](https://www.sagemath.org/) will make metaprogramming in this system very powerful. I maintain the option to just trust these results but hopefully they can be translated into arguments the kernel can understand.

The core logic is more or less multi-sorted first order logic aka [SMT-LIB2](https://smt-lib.org/).

Big features that ATPs do not often support are induction, definitions, and other axiom schema. Knuckledragger supports these.

Other theorem provers of interest: [cvc5](https://cvc5.github.io/), [Vampire](https://vprover.github.io/), [eprover](https://wwwlehre.dhbw-stuttgart.de/~sschulz/E/E.html), [Twee](https://nick8325.github.io/twee/), [nanoCoP](https://leancop.de/nanocop/).

The de Bruijn criterion is going to be bent or broken in certain senses. Attention is paid to what is kernel and what is not. Proof objects are basically trees recording chains of lemmas discharged by Automated Theorem Prover (ATP) calls. Soundness will be attempted, accidental misuse will be made difficult but not impossible.

Isabelle and ACL2 are the strongest influences. If you want dependent type theory, you are at a level of investment and sophistication that it behooves you to be in another system. Should there be a strong automated DTT solver someday, I will reconsider.

I maintain the right to change my mind about anything.

TODO: A no-install WIP colab tutorial is available [here](http://colab.research.google.com/github/philzook58/knuckledragger/blob/main/tutorial.ipynb)
