# Knuckledragger

[![Open In Colab](https://colab.research.google.com/assets/colab-badge.svg)](http://colab.research.google.com/github/philzook58/knuckledragger/blob/main/tutorial.ipynb)

<img src="https://raw.githubusercontent.com/philzook58/knuckledragger/main/logo.webp" alt="drawing" width="200" align="left"/>

Knuckledragger is an attempt at creating a down to earth, highly automated interactive proof assistant in python. It is not attempting to be the most interesting, expressive, or flexible logic in the world. The goal is to support applications like software verification, calculus, equational reasoning, and numerical bounds. A no-install colab tutorial is available [here](http://colab.research.google.com/github/philzook58/knuckledragger/blob/main/tutorial.ipynb)

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

- [Knuckledragger: Experimenting with a Python Proof Assistant](https://www.philipzucker.com/python-itp/)
- [Experiments in the Irrationality of Sqrt 2 with SMT](https://www.philipzucker.com/sqrt2/)
- [Peano Nats in Interactive SMT](https://www.philipzucker.com/sqrt2_2/)
- [Proving Sum n = n*(n-1)/2 and that 1/n tends to 0](https://www.philipzucker.com/analysis_knuckle/)

## Design

Using widespread and commonly supported languages gives a huge leg up in terms of tooling and audience.

It is not desirable or within my capabilities to build a giant universe in which to live. The goal is to take a subtle blade and bolt together things that already exist.

The de Bruijn criterion is going to be bent or broken in certain senses. The kernel will be small. It is still of matter of design whether to have checkable proof objects or a controlled checking process.

Soundness will be attempted, accidental misuse will be made difficult but not impossible.

Core functionality comes from Z3 and other ATPs. To some degree, this is a metalayer to guide automated provers down proofs they could perhaps do on their own, but of course would get lost. The core logic is more or less multi-sorted first order logic.

A big feature that ATP do not often support is induction, definitions, and other axiom schema. These are supported.

A hope is to be able to use easy access to Jupyter, copilot, ML ecosystems, sympy, cvxpy, numpy, scipy, calcium, flint, sage, singular will make metaprogramming this system very powerful. I maintain the option to just trust these results but hopefully they can be translated into arguments the kernel can understand.
