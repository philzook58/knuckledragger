# Knuckledragger Development Guide

- Try to follow the style that already exists in the repo
- Simple and non verbose is much preferred
- Recommend changes to improve clarity of error messages
- Recommend changes to make more consistent with Lean/Rocq/Isabelle/ACL2 conventions
- Recommend new features that this system is missing that Lean/Rocq/Isabelle/ACL2/Mizar might have
- Record new learnings in this file to avoid repeating failures
- I am worried about proof instability and solve time. So try to keep track of those.
- Actually run the file using `time python` to make sure proofs go through. A file should not take longer than 0.5s
- Do not just fill up on junk theorems with little content. Make theorems if useful, but sheer bulk of content is bad since I need to manually review it.
- Some problems are things that should be improved. Do not always just silently find a workaround. Parser errors in valid lean syntax should be improved.
- You may sometimes need new axioms (rarely), but ask me before you add them.
- Add comments into proofs to explain the rough lines of what you are doing
- Try to simplify proofs by factoring any common moves like `unfold` or `rw` above the branches of cases or splits.
- Big jumps for the solver are slow, but so is too many little steps. There is a balance.
- DO NOT try to be sneaky to get a proof though (mutating stuff, using python craziness). Knuckledragger relies on proper usage to remain sound.

## Library Usage

Knuckledragger is a python library for interactive theorem proving backed by Z3.

### Core Types

- `kd.Proof` - A proven theorem (frozen dataclass with `thm: smt.BoolRef`)
- `smt.BoolRef` - Z3 boolean formula (theorems/propositions)
- `smt.ExprRef` - Z3 expression (terms)
- `smt.SortRef` - Z3 sorts/types (e.g., `smt.IntSort()`, `smt.RealSort()`)

Many proof and tactic functions can also take a string in simple Lean-like syntax. This can improve readability and reduce verbosity

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
  - **Important**: After `l.induct(x)` on an inductive datatype, the constructor case generates `ForAll` for ALL constructor fields
  - For `Cons(head, tail)` you must use `head, tail = l.fixes()` not `l.fix()`
  - Example: After inducting on a list, the `Cons` case needs `fixes()` to open both head and tail

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

### Common Proof Patterns

**Tactic-style (Lean/Rocq): Simple and direct**

```python
@kd.Theorem(smt.ForAll([l], my_property(l)))
def my_lemma(pf):
    _l = pf.fix()
    pf.induct(_l)
    # Base case (e.g., Nil)
    pf.auto(by=[relevant_defns])
    # Constructor case (e.g., Cons) - use fixes() for all fields!
    _head, _tail = pf.fixes()
    pf.auto(by=[relevant_defns, helper_lemmas])
```

**Isar-style (Isabelle): Explicit forward reasoning with have/show**

```python
@kd.Theorem(smt.ForAll([l1, l2], sum(append(l1, l2)) == sum(l1) + sum(l2)))
def sum_append(pf):
    _l1, _l2 = pf.fixes()
    pf.induct(_l1)
    # Base case - establish facts with have, finish with auto
    pf.have(append(Nil, _l2) == _l2, by=[append.defn])
    pf.have(sum(Nil) == 0, by=[sum.defn])
    pf.auto(by=[append.defn, sum.defn])  # Discharge accumulated implications
    # Inductive case
    _head, _tail = pf.fixes()
    pf.have(append(Cons(_head, _tail), _l2) == Cons(_head, append(_tail, _l2)), by=[append.defn])
    pf.auto(by=[append.defn, sum.defn])
```

**Important about `have` and `show`:**

- `pf.have(fact, by=[...])` adds `fact -> goal` as the new goal (forward reasoning)
- After multiple `have` statements, use `pf.auto()` to discharge all accumulated implications
- `pf.show(exact_goal, by=[...])` checks the goal matches exactly, then proves it
- Isar-style is more verbose but shows explicit reasoning steps
- Tactic-style is more concise and lets Z3 do more work

**Passing lemmas to `by=`:**

- Use `by=[lemma1, lemma2]` to provide previously proved theorems
- Z3 will use these as assumptions
- Sometimes you need to pass helper lemmas that seem "obvious" to help Z3 find the proof
- Order can matter - Z3 may need earlier lemmas to prove later steps

**When proofs timeout:**

- Break into smaller lemmas
- Prove helper lemmas first and use them in `by=`
- Check if you need identity lemmas (e.g., `append(l, Nil) == l` before `rev_append`)
- Consider increasing `timeout` parameter to `l.auto(by=[...], timeout=5000)`

### Theory Status

**Stable/Mature** (good examples):

- `kdrag.theories.int` - integer arithmetic with induction
- `kdrag.theories.nat` - Peano naturals (excellent induction examples)
- `kdrag.theories.logic.zf` - ZF set theory (excellent proof examples)
- `kdrag.theories.seq` - sequences
- `kdrag.theories.list` - polymorphic lists (use only if needed, prefer monomorphic versions)
- `examples/intlist.py` - pedagogical example of integer lists with many proofs

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
