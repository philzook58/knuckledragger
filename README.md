# Knuckledragger

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](http://colab.research.google.com/github/philzook58/knuckledragger/blob/main/tutorial.ipynb)

<img src="https://raw.githubusercontent.com/philzook58/knuckledragger/main/logo.webp" alt="drawing" width="200" align="left"/>

Knuckledragger is an attempt at creating a down to earth, highly automated interactive proof assistant in python. It is not attempting to be the most interesting, expressive, or flexible logic in the world. The goal is to support applications like software/hardware verification, calculus, equational reasoning, and numerical bounds. A no-install colab tutorial is available [here](http://colab.research.google.com/github/philzook58/knuckledragger/blob/main/tutorial.ipynb)

<br clear="left"/>

## Installation

```bash
python3 -m pip install git+https://github.com/philzook58/knuckledragger.git
```

Or to install locally

```bash
git clone https://github.com/philzook58/knuckledragger.git
cd knuckledragger
python3 -m pip install -e .
```

## Blog Posts

- [State of Knuckledragger, a Semi-Automated Python Proof Assistant](https://www.philipzucker.com/state_o_knuck/)
- [Proving Sum n = n*(n-1)/2 and that 1/n tends to 0](https://www.philipzucker.com/analysis_knuckle/)
- [Peano Nats in Interactive SMT](https://www.philipzucker.com/sqrt2_2/)
- [Experiments in the Irrationality of Sqrt 2 with SMT](https://www.philipzucker.com/sqrt2/)
- [Knuckledragger Update: ATP for Python Interactive Theorem Proving](https://www.philipzucker.com/knuckledrag2/)
- [Knuckledragger: Experimenting with a Python Proof Assistant](https://www.philipzucker.com/python-itp/)

## Design

It is not desirable or within my capabilities to build a giant universe in which to live. The goal is to take a subtle blade and bolt together things that already exist.

Using widespread and commonly supported languages gives a huge leg up in terms of tooling and audience. Python is the modern lingua franca of computing. It has a first class interactive experience and extensive bindings to projects in other languages.

Core functionality comes from [Z3](https://github.com/Z3Prover/z3). The Z3 python api is a de facto standard. The term and formula data structures of knuckledragger are literally smt python terms and formula. To some degree, knuckledragger is a metalayer to guide smt through proofs it could perhaps do on its own, but it would get lost.

A hope is to be able to use easy access to [Jupyter](https://jupyter.org/), [copilot](https://copilot.microsoft.com/), ML ecosystems, [sympy](https://www.sympy.org/), [cvxpy](https://www.cvxpy.org/), [numpy](https://numpy.org/), [scipy](https://scipy.org/), [egglog](https://egglog-python.readthedocs.io/latest/), [Julia](https://github.com/JuliaPy/PythonCall.jl), [Prolog](https://www.swi-prolog.org/pldoc/man?section=janus-call-prolog), [Maude](https://fadoss.github.io/maude-bindings/), [calcium](https://fredrikj.net/calcium/), [flint](https://fredrikj.net/python-flint/), [Mathematica](https://reference.wolfram.com/language/WolframClientForPython/), and [sage](https://www.sagemath.org/) will make metaprogramming in this system very powerful. I maintain the option to just trust these results but hopefully they can be translated into arguments the kernel can understand.

The core logic is more or less multi-sorted first order logic aka [SMT-LIB2](https://smt-lib.org/).

Big features that ATPs do not often support are induction, definitions, and other axiom schema. Knuckledragger supports these.

Other theorem provers of interest: [cvc5](https://cvc5.github.io/), [Vampire](https://vprover.github.io/), [eprover](https://wwwlehre.dhbw-stuttgart.de/~sschulz/E/E.html), [Twee](https://nick8325.github.io/twee/), [nanoCoP](https://leancop.de/nanocop/).

The de Bruijn criterion is going to be bent or broken in certain senses. Attention is paid to what is kernel and what is not. Proof objects are basically trees recording chains of lemmas discharged by Automated Theorem Prover (ATP) calls. Soundness will be attempted, accidental misuse will be made difficult but not impossible.

Isabelle and ACL2 are the strongest influences. If you want dependent type theory, you are at a level of investment and sophistication that it behooves you to be in another system. Should there be a strong automated DTT solver someday, I will reconsider.

I maintain the right to change my mind about anything.
