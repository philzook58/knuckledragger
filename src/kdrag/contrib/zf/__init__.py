"""Exploratory ZF set theory awaiting manual review and promotion to theories.

Builds on `kdrag.theories.zf.zf`, following Halmos' Naive Set Theory.

Modules: `nat` for the von Neumann naturals, ω, and the Peano axioms
(Halmos §11-12); `fun` for functions as sets of pairs (Halmos §8); `rec` for
the recursion theorem on ω (Halmos §12); `arith` for addition and
multiplication defined by recursion (Halmos §13); `order` for the order on ω,
where `m < n` is `m ∈ n` (Halmos §13); `finite` for equivalent and finite
sets via HOL-function bijections (Halmos §13); `card` for comparing sizes and
the Schröder-Bernstein theorem (Halmos §22); `poset` for partial, total, and
well orders (Halmos §14, §17); `ordinal` for the axiom of substitution
(Replacement) and ordinal numbers (Halmos §19); `trec` for the transfinite
recursion theorem (Halmos §18); `sim` for similarity of ordered sets (Halmos
§18). Dependencies flow one way: `nat` and `fun` are independent, `rec` uses
both, `arith` uses `rec`, `order` uses `arith`, `finite` and `poset` use
`order`, `card` uses `finite`, `ordinal` uses `poset` and `finite`, and `trec`
and `sim` use `poset` (`sim` also uses `finite`); `ordset` for sets of ordinal
numbers (Halmos §20) uses `ordinal` and `sim`. Only `ordinal` and `ordset` may
use Replacement and definite description.
"""
