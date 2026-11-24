# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- Add `contrib.analysis` proofs of real function limit uniqueness and derivative rules for constants, identity, addition, scalar multiplication, continuity, and composition.
- Add `contrib.analysis.rseq.lim_lemma` to compose sequence-limit rules, including arithmetic expressions in an index and the known limit of `1/n`.
- Add `kdrag.contrib.analysis.integral`: the gauge (Henstock-Kurzweil) integral, Cousin's lemma, uniqueness of integrals, and the fundamental theorem of calculus in `kdrag.contrib.analysis.ftc`.
- Add `finsum_sub`, `finsum_diff` (telescoping), and `abs_finsum_le` in `contrib.analysis.finsum`.
- Add `contrib.zf.nat`: the axiom of infinity, von Neumann ω as the smallest inductive set, induction over ω (with an `induct_omega` hook for `l.induct`), and the Peano axioms following Halmos §12.
- Add `contrib.zf.fun` (functions as sets with a choice-free `app`) and `contrib.zf.rec`: the recursion theorem on ω, with `nat_rec(X, a, F)` as Halmos' smallest closed set of pairs and theorems `nat_rec_is_func`, `nat_rec_zero`, `nat_rec_succ`.
- Add `contrib.zf.arith`: addition and multiplication on ω by recursion (Halmos §13), with `add_zero`, `add_succ`, `zero_add`, `succ_add`, `add_comm`, `add_assoc`, `mul_zero`, `mul_succ`, `zero_mul`, `succ_mul`, `mul_comm`, `mul_assoc`, and the distributive law `mul_add`.
- Add `contrib.zf.order`: comparability and trichotomy of natural numbers (`nat_comparable`, `nat_elem_asymm`), `elem_iff_le_ne`, `nat_le`, compatibility of `∈` with addition and multiplication, and the well-ordering `exists_least_of_nonempty` (Halmos §13).
- Add `contrib.zf.finite`: one-to-one correspondences as HOL functions (`fun.maps_to`, `inj_on`, `surj_on`, `bij_on`), the equivalence relation `equivalent`, `omega_equivalent_sub_zero`, the pigeonhole principle `nat_eq_of_equivalent_le`, `finite`, uniqueness of the number of elements, and `omega_infinite` (Halmos §13). Generalize `rec.maps_to` to `fun.maps_to(F, X, Y)`.
- Keep `contrib.zf` choice-free: build `nat_rec` from a choice-free intersection `fun.sinter` instead of the `pick`-based `biginter`, prove `pair_elem_prod` without `fst`/`snd`, and invert correspondences with `finite.inv` (`⋃{x ∈ A | F x = y}`). A test checks the proofs use only the ZF axioms of `theories.zf` and infinity.
- Add `contrib.zf.card`: domination `dominated(X, Y)` and the Schröder-Bernstein theorem `schroeder_bernstein` following Halmos §22, without choice.
- Add `contrib.zf.poset`: partial, total, and well orders as HOL relations on a set (Halmos §14, §17), least and minimal elements, initial segments `seg`, inclusion as a partial order, `total_order_of_well_order`, `omega_well_order`, and `seg_nat` (each natural number is the set of its predecessors).
- Add `contrib.zf.ordinal`: the axiom of substitution (Replacement) as `repl(F, A)` with `elem_repl`, and Halmos' ordinal numbers with `is_ordinal_iff` (well ordered by ∈, transitive, irreflexive), `omega_is_ordinal`, `nat_is_ordinal`, `is_ordinal_of_elem`, and `is_ordinal_succ`. The axiom test tracks which modules use Replacement.
- Add the principle of transfinite induction `poset.well_order_induction` (Halmos §17) and `contrib.zf.trec`, the transfinite recursion theorem (Halmos §18): for a well ordered W and a sequence function F of type W in X, `trec(F, R, W, X)` is a function from W into X with `trec_eq`: U(a) = F(U^a). No Replacement is used.
- Add `contrib.zf.sim`: order embeddings and similarities (Halmos §18), Halmos' lemma `le_apply_of_order_embedding` (a ≤ f(a) for an order-preserving self-map of a well ordered set), `similarity_unique`, and `not_similarity_seg`.
- Add definite description `ordinal.the` with axiom `the_eq` (as Isabelle's THE; it picks only unique objects and adds no choice), and `contrib.zf.ordset` (Halmos §20): `eq_of_similarity` (similar ordinals are equal), `ordinal_comparable`, `is_ordinal_inter`, `elem_of_transitive_ssubset`, `exists_least_of_ordinals`, and `is_ordinal_of_transitive`.
- Add `contrib.zf.count`, Halmos' counting theorem: `counting_theorem` (each well ordered set is similar to the ordinal `ord_of(R, X)`) and `ordinal_similar_unique`, proved by collecting the ordinals of initial segments with Replacement. Add `sim.similarity_inv`, `similarity_comp`, `similarity_seg`, and `poset.elem_seg_iff`, `seg_seg`, `partial_order_refl`.
- Add to `contrib.zf.ordset` (Halmos §20): `is_ordinal_bigunion` with `le_bigunion` and `bigunion_le` (the union of a set of ordinals is their supremum), `ordinal_elem_iff_ssubset`, and the Burali-Forti paradox `burali_forti`.
- Add `contrib.zf.oarith` (Halmos §21): the ordinal sum `osum_set`/`osum_rel` with `osum_well_order`, ordinal addition `oadd(α, β) = ord_of(⊕, α ⊕ β)`, `oadd_zero`, `oadd_one` (α + 1 = α⁺), `one_oadd_omega` (1 + ω = ω), `oadd_not_comm`, `zero_oadd` (0 + α = α), and `oadd_assoc`, via `similarity_osum` (similar summands give similar sums) and `similarity_osum_assoc`; `sim.similar_refl`/`similar_symm`/`similar_trans`. Add the choice-free first coordinate `fun.pfst` with `pfst_pair`, and name the counterexample set in `well_order_induction` (`poset.without`).

### Changed

- `ProofState.obtain` now returns `(witness, fact)` or `(witnesses, fact)` for multiple binders. Use `witness, _ = l.obtain(h)` when the witness alone is needed.

- Use one `contrib.analysis.deriv.has_deriv_at(f, a, p)` definition via the punctured difference-quotient limit. Prove the remainder estimate as `has_deriv_at_iff_remainder`; rename the former `has_diff_at` rules accordingly.
- Order `contrib.analysis.rseq.has_lim_smul` binders as scalar, sequence, limit for composition by `lim_lemma`.

### Removed

## [0.4.0]

### Added

- Add continuity and limit lemmas for real functions, and a nonnegativity theorem for limits of real sequences.
- Add theorem search to the documentation, with pretty-printed statements and links to source.
- Add `pretty_expr`, `pretty_goal`, and custom infix registration. `PTheorem` uses the compact goal printer for proof development.
- Add solver-free `exact(statement, proof)` with universal instantiation, shared by the `exact` tactic.
- Accept `"z3"`, `"cvc5"`, `"vampire"`, and `"eprover"` as solver names in `prove`.

### Changed

- `ForAll(xs, p, q, r)` now means `∀ xs, p → q → r`. Write `ForAll(xs, And(p, q), r)` when a tactic needs a single conjunctive premise.
- `have` returns the introduced formula. `specialize` can apply terms and premise evidence in one call, starting from a hypothesis or a proof.
- The sequence predicate `has_lim` now requires its cutoff witness to be nonnegative.
- Require Z3 5.3.3 or newer, and install packaged E prover and Vampire through the `solvers` extra. Improve external prover translations and add macOS CI coverage.

### Fixed

- Fix chained proof application and print binary `Distinct` as `≠` in the pretty printer.

### Removed

- Remove the `forward` tactic. Use `specialize` with the implication and its premise.

## [0.3.0] - 2026-05-07

- Published version 0.3.0 to PyPI.

## [0.1.3] - 2025-11-16

- Initial release. Project has been developed since 2024-01-01

[Unreleased]: https://github.com/philzook58/knuckledragger/compare/v0.4.0...HEAD
[0.4.0]: https://github.com/philzook58/knuckledragger/compare/v0.3.0...v0.4.0
[0.3.0]: https://github.com/philzook58/knuckledragger/releases/tag/v0.3.0
[0.1.3]: https://github.com/philzook58/knuckledragger/releases/tag/v0.1.3
