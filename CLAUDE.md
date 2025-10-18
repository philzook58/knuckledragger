# Knuckledragger Development Guide

- Try to follow the style that already exists in the repo
- Simple and non verbose is much preferred

## Library Usage

Knuckledragger is a python library for interactive theorem proving backed by Z3.

### Core Types

- `kd.Proof` - A proven theorem (frozen dataclass with `thm: smt.BoolRef`)
- `smt.BoolRef` - Z3 boolean formula (theorems/propositions)
- `smt.ExprRef` - Z3 expression (terms)
- `smt.SortRef` - Z3 sorts/types (e.g., `smt.IntSort()`, `smt.RealSort()`)

### Z3 Basics (from `kdrag.smt`)

Common functions:
- `smt.Const(name, sort)` or `smt.Ints("x y z")`, `smt.Reals("x y z")`
- `smt.ForAll(vs, body)`, `smt.Exists(vs, body)`
- `smt.And(...)`, `smt.Or(...)`, `smt.Implies(p, q)`
- `smt.Function(name, *arg_sorts, ret_sort)` - declare uninterpreted function

Operators naturally overload: `+`, `-`, `*`, `/`, `==`, `!=`, `<`, `>`, `<=`, `>=`

### Simple Proofs

`kd.prove(thm, by=[lemma1, lemma2], timeout=1000)` - Prove a theorem in one Z3 call
- Returns a `kd.Proof` object
- Use `by=[...]` to provide lemmas as assumptions
- Throws `kd.kernel.LemmaError` if unprovable

### Proof State Tactics (Preferred: `@Theorem` decorator)

**Modern style** (preferred):
```python
@kd.Theorem(smt.ForAll([x], x + 0 == x))
def add_zero(l):
    """x + 0 == x"""
    x = l.fix()
    l.auto()
```

**Old style** (less preferred):
```python
l = kd.Lemma(smt.ForAll([x], x + 0 == x))
x = l.fix()
l.auto()
add_zero = l.qed()
```

For development, use `@kd.PTheorem` which prints next goal instead of erroring.

### Tactics Reference

Tactics are methods on `ProofState` (returned by `kd.Lemma` or passed to `@Theorem`):

**Opening quantifiers/assumptions:**
- `l.fix()` - open one ∀, returns the fresh variable
- `l.fixes()` - open multiple ∀s, returns list
- `l.intros()` - move implication hypothesis into context
- `l.obtain(n)` - open ∃ in hypothesis `n`, returns witness constants

**Proving subgoals:**
- `l.auto(**kwargs)` - call Z3 on current goal with context
- `l.show(thm, by=[...])` - prove goal equals `thm` using lemmas
- `l.exact(pf)` - close goal with proof `pf`

**Manipulating context/goal:**
- `l.have(thm, by=[...])` - add lemma to context (must be implied by context)
- `l.rw(rule, at=None, rev=False)` - rewrite using equality `rule` (at goal or hyp index)
- `l.unfold(*decls, at=None)` - unfold definitions
- `l.split()` - split `∧` in goal or `∨` in hypotheses
- `l.apply(n)` - apply implication from hypothesis `n`
- `l.exists(*ts)` - provide witnesses for ∃ goal

**Induction:**
- `l.induct(x, using=None)` - induct on variable `x` (auto-detects or use custom principle)

**Advanced:**
- `l.specialize(n, *ts)` - instantiate universal in hypothesis `n` with terms
- `with l.sub() as l1: ...` - create subgoal

**Finish:**
- `l.qed()` - complete proof and return `kd.Proof`

### Definitions and Axioms

- `kd.define(name, vars, body)` - Define a function. Returns function with `.defn` attribute
- `kd.axiom(thm)` - Assert axiom (use sparingly!)
- `kd.FreshVar(name, sort)` or `kd.FreshVars("x y z", sort)` - Create schema variables

### Algebraic Datatypes

```python
List = kd.Inductive("List")
List.declare("Nil")
List.declare("Cons", ("head", smt.IntSort()), ("tail", List))
List = List.create()
```

- `kd.Struct(name, *fields)` - Product types
- `kd.NewType(name, basesort, pred)` - Refinement types
- `kd.Enum(name, *constructors)` - Simple enums
- `kd.InductiveRel(name, *params)` - Inductively defined relations

### Quantifier Helpers

- `kd.QForAll([x], hyp, body)` → `ForAll([x], Implies(hyp, body))`
- `kd.QExists([x], hyp, body)` → `Exists([x], And(hyp, body))`
- `kd.QImplies(hyp, conc)` → sugar for conditional implications

### Calc (Equational Reasoning)

```python
c = kd.Calc([x], lhs)
c.eq(rhs1, by=[lemma1])
c.eq(rhs2, by=[lemma2])
result = c.qed()
```

Supports `.eq`, `.le`, `.lt`, `.ge`, `.gt` for chained reasoning.

### Theory Status

**Stable/Mature** (good examples):
- `kdrag.theories.int` - integer arithmetic with induction
- `kdrag.theories.nat` - Peano naturals
- `kdrag.theories.logic.zf` - ZF set theory (excellent proof examples)
- `kdrag.theories.seq` - sequences
- `kdrag.theories.list` - lists

**Experimental** (avoid for examples):
- `kdrag.theories.algebra.*` - category theory, groups, etc.
- `kdrag.theories.real.calc` - needs updating

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
