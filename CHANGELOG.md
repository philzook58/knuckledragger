# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

### Changed

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
