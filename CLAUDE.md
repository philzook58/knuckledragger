# Knuckledragger Development Guide

- Use existing .venv python if available, otherwise create a venv and install using `uv pip install -e[solvers,rust,pypcode,dev]`
- Try to follow the style that already exists in the repo
- Simple and non verbose is much preferred
- Solver instability and solve time are ALWAYS a concern. Track them.
- Recommend changes to improve clarity of error messages
- Recommend changes to make more consistent with Lean/Rocq/Isabelle/ACL2 conventions
- Proactively suggest definition and theorem renames that align with mathlib conventions, adapting to Python snake_case. Check the corresponding mathlib names when practical; include `exists_` for existence results and operation names such as `_neg` when needed to make the statement clear.
- Recommend new features that this system is missing that Lean/Rocq/Isabelle/ACL2/Mizar might have
- Record new learnings in this file to avoid repeating failures
- Actually run the file using `time python` to make sure proofs go through. A file should not take longer than 0.5s
- Do not just fill up on junk theorems with little content. Make theorems if useful, but sheer bulk of content is bad since I need to manually review it.
- Some problems are things that should be improved. Do not always just silently find a workaround. Parser errors in valid lean syntax should be improved.
- You may sometimes need new axioms (rarely), but ask me before you add them.
- Add comments into proofs to explain the rough lines of what you are doing
- Try to simplify proofs by factoring any common moves like `unfold` or `rw` above the branches of cases or splits.
- Big jumps for the solver are slow, but so is too many little steps. There is a balance.
- DO NOT try to be sneaky to get a proof though (mutating stuff, using python craziness). Knuckledragger relies on proper usage to remain sound.

## Review boundary and proof presentation

- `kdrag.theories` is the curated library for mathematics Philip has carefully reviewed and understands. Keep new or less-reviewed mathematics in `kdrag.contrib`; use `kdrag.contrib.analysis` for exploratory real analysis and `kdrag.contrib.zf` for exploratory set theory following Halmos.
- Philip will manually promote material into `kdrag.theories`. Do not promote it, or move existing reviewed material out, without an explicit request.
- Use the single derivative predicate `contrib.analysis.deriv.has_deriv_at(f, a, p)`, defined via `has_lim_at`. Derive alternative characterizations as theorems rather than introducing parallel derivative predicates.
- In `contrib.analysis`, keep pointwise limits/continuity in `cont`, derivative predicates and derivative-only lemmas in `deriv`, sequence limits in `rseq`, finite sums in `finsum`, gauge-integral construction in `integral`, and the derivative/integral connection in `ftc`. Keep dependencies one-way; `integral` must not depend on `deriv` or `ftc`.
- Compare both folders for existing definitions and reusable theorems before adding mathematics. Contrib may import theories; theories must not import contrib. Keep exploratory definitions separate from existing theory declarations until promotion.
- If the layout or a proposed change conflicts with this boundary, point it out rather than silently treating it as permission to change the policy.
- When responding about added or changed mathematics, include the actual definition code, theorem statements, and complete proof bodies in chat, as they appear in the source. Summaries and file links supplement the code; they do not replace it. Keep changes small enough to review this way.

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
- `l.intro()` - move one implication hypothesis into context and return it.
- `l.intros()` - introduce all leading implications and return their hypotheses as a list; stop before `ForAll` and leave conjunctions grouped.
- `l.obtain(n)` - open ∃ in hypothesis `n`, returns `(witness, fact)` (a list of witnesses for multiple binders)

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
- `kd.define_const(name, body)` - Define a constant expression with `.defn`; `define(name, [], body)` returns a nullary function declaration.
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

- `ForAll([x], h1, h2, body)` and `kd.QForAll([x], h1, h2, body)` curry premises as `∀ x, h1 → h2 → body`. Use an explicit `And(h1, h2)` for a grouped premise.
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

- **Test**: `pytest`
- **Lint**: `ruff check`
- **Type Check**: `uvx ty check`

## Code Style

- **Imports**: Group standard library, third-party, and local imports
- In theories and examples, import proof and SMT helpers explicitly (`from kdrag import prove, Theorem`; `from kdrag.smt import ForAll, Implies`). Keep qualification where names would clash.
- **Types**: Use type annotations for function parameters and return values
- **Formatting**: Follow PEP 8 guidelines; ruff handles formatting
- **Docstrings**: Include for public functions and classes
- **Function Names**: snake_case for functions, CamelCase for classes
- **Lemma Names**: Follow mathlib names where practical, adapting to snake_case and existing predicates. Prefer `const`, `id`, and `conclusion_of_hypothesis`.
- **Error Handling**: Use exceptions for failure conditions with clear messages
- **Test Names**: Prefix with `test_` and descriptively name the behavior

## Test Reliability Notes

- Use `smt.substitute_body(q, *terms)` for binder substitution; it checks sorts and reverses binder-order arguments internally. Z3 can silently leave loose bound variables on sort mismatches. Convenience APIs should cast Python literals to the binder sort; kernel rules require already-sorted expressions.

- Automatic lifting creates lambdas with fresh binder names. Compare results semantically rather than with AST `.eq`, and instantiate lemmas at concrete arguments when quantifier matching through lambda arguments is unstable.
- Sequence concatenation accepts Python lists (`[x] + xs`, `xs + [x]`), delegating typed literal conversion to `cast.cast`. Bare elements are rejected with a singleton hint; native scalar additions must defer sequence RHS operands so that diagnostic can run.
- Default induction on a sequence uses empty/cons cases through `notation.induct`. Explicit `notation.induct_seq` retains empty/singleton/concatenation induction; no sequence-theory import is needed for the default.
- `cases(p, q, ...)` checks coverage under the current context before mutating the state; branches follow argument order. A single argument retains Boolean or datatype case splitting.
- For quantified witness proofs, fix the outer parameters and instantiate the defining theorem before `auto`.
- Check free schema variables on the original theorem before opening binders; Z3 may recycle collected schema-variable IDs.
- CFFI compilation should use `compile(tmpdir=...)` rather than change the process working directory.

- When restating nested quantified witnesses, match the definition's binder names and comparison direction (`RealVal(0) < t` versus `t > 0`) to avoid unstable equivalence searches.
- `p == ForAll(...)` builds `ForAll(...) == p`, because `QuantifierRef`'s reflected `__eq__` wins. Use `smt.Eq(p, q)` when the orientation matters, such as a lemma meant for `rw`.
- For sequence limit proofs, rewrite the goal with `has_lim_iff` and combine `eventually_near` facts with `eventually_and` and finish with `eventually_mono`, instead of choosing the larger N by hand. Turn `∀ n ≥ 0` hypotheses into `eventually` facts with `eventually_of_forall_nonneg`. One-shot `auto` over unfolded `has_lim` is fragile: adding unrelated declarations can make it time out.
- `l.obtain(h)` replaces `h` with the witness fact and returns both the witness and the fact. Use the returned fact by name. `l.unfold(..., at=h)` replaces `h` in place. `l.specialize(h, ...)` consumes `h` and returns the new hypothesis.
- In long proofs, keep defined predicates folded in the context and pass instantiated definitions such as `is_fine.defn(D, xs, ts, n)` in `by=`. Unfolded quantified hypotheses make later `auto` calls time out or depend on import order. Clear quantified hypotheses once they have been used.
- Give witnesses involving division explicitly with `l.exists`, then `obtain` a fresh constant for them (e.g. `eta` with `eta * (|b - a| + 1) == eps`). Division terms inside later goals cause nonlinear timeouts.
- `0 <= x` in Python builds `x >= 0`. Write `RealVal(0) <= x` when a `have` must match an instantiated lemma premise syntactically.
- For pointwise choice of a function (e.g. gauges), use `contrib.analysis._choice.axiom_of_choice` and state the premise with its binder names `x` and `y`.
- Isolate extensional or rational identities from quantified limit hypotheses when proving derivative rules; import-order tests can reveal timeouts hidden by a standalone import.
- In `contrib.zf`, prove inequalities of sets from one witnessing element (`x ∈ succ x`, `x ∉ ∅`) rather than through `ext_ax`; congruence finishes it. Use `l.induct(n, using=nat.induct_omega)` for induction over ω.
- Proving `sep(ω, P) == ω` in one `have` timed out; state the three hypotheses of `eq_omega_of_inductive` as separate `have`s first.


## Proof instability reports

- Treat proof timeouts that vary with platform, solver version, seed, import order, term construction, or irrelevant context as reproducibility problems to investigate alongside the proof fix.
- Preserve the original failing query and its options before changing the proof when possible. Record the source commit, platform, Python/Z3 versions, seed, timeout/resource limits, result, `reason_unknown()`, and timing or solver statistics. CI should retain failing SMT dumps when available.
- Reduce the case to a small standalone SMT-LIB file or Z3 Python program requiring no knuckledragger imports. Remove irrelevant hypotheses and structure while checking that the observed behavior survives. Keep both the original export and the reduced reproducer when useful.
- Run failing and passing variants in fresh processes, changing one factor at a time. Include the expected result and exact commands. Distinguish a reproduced original failure from a related reduced example, a resource-budget demonstration, or an unreproduced platform-specific report.
- Search the knuckledragger issue tracker for an existing report; add the reproducer there or open a succinct issue linking the source/CI failure, standalone reproducer, observed results, and workaround. Philip has requested this as the standard workflow for proof-instability problems. Update reports when later evidence changes the diagnosis.
