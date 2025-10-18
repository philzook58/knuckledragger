# Knuckledragger Development Guide

- Try to follow the style that already exists in the repo
- Simple and non verbose is much preferred

## Library Usage

Knuckledragger is python library for interactive theorem proving.

The theorem `smt.BoolRef` and formula `smt.ExprRef` are those reexported from z3py in the module `kdrag.smt`.
Commonly used z3py functions are

- `smt.Const(name, sort)`
- `smt.ForAll(vs, body)`
- `smt.Exists(vs, body)`
- `smt.And` `smt.Or` `smt.Implies`

Many things ave natural operator overloading available for them

It has a tactics system available in `kdrag.tactics`. Tactics are methods attached to a `kd.tactics.ProofState` object which can be made `l = kd.Lemma(my_to_be_proven_formula)`. This moves around the proof state in a manner similar to Lean or Rocq or Isabelle.

Common tactics include

- `l.intros` - bring an implication into the context
- `l.fix()` or `l.fixes` - open a forall quantifier
- `l.obtain(n)`  will open an existential in the context. This function returns the fresh constants produces
- `l.have(mythm)` where mythm is implied by the current context will add mythm into the context
- `l.rw(add_assoc)` to apply a rewrite rule lemma
- `l.exists` to fill in a existential at the top level of the current goal

`l.qed()` is the call that actually produces a

Proofs dischargeable by a single z3 call can be discharged via `kd.prove(thm, by=[lemma1, lemma2, lemma3])` which returns a `kd.Proof` object

Good examples of usage can be found in `kdrag.theories.real`, `kdrag.theories.logic.zf`

## Commands

- **Test**: `pytest -m "not slow"`
- **Lint**: `ruff check`
- **Type Check**: `pyright`

## Code Style

- **Imports**: Group standard library, third-party, and local imports
- **Types**: Use type annotations for function parameters and return values
- **Formatting**: Follow PEP 8 guidelines; ruff handles formatting
- **Docstrings**: Include for public functions and classes
- **Function Names**: snake_case for functions, CamelCase for classes
- **Error Handling**: Use exceptions for failure conditions with clear messages
- **Test Names**: Prefix with `test_` and descriptively name the behavior
