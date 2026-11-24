"""Exploratory ZF set theory awaiting manual review and promotion to theories.

Builds on `kdrag.theories.zf.zf`, following Halmos' Naive Set Theory.

Modules: `nat` for the von Neumann naturals, ω, and the Peano axioms (Halmos
§11-12), with the small naturals 1 and 2; `dsum` for disjoint unions A × {0} ∪
B × {1}, used by ordinal and cardinal sums; `fun` for functions as sets of
pairs (Halmos §8); `rec` for the recursion theorem on ω (Halmos §12); `arith`
for addition and multiplication defined by recursion (Halmos §13); `order` for
the order on ω, where `m < n` is `m ∈ n`, and parity via `bit` (Halmos §13);
`finite` for equivalent and finite sets via HOL-function bijections (Halmos
§13); `card` for comparing sizes and the Schröder-Bernstein theorem (Halmos
§22); `poset` for partial, total, and well orders (Halmos §14, §17); `ordinal`
for the axiom of substitution (Replacement) and ordinal numbers (Halmos §19);
`trec` for the transfinite recursion theorem (Halmos §18); `sim` for similarity
of ordered sets (Halmos §18). Dependencies flow one way: `nat` and `fun` are
independent, `rec` uses both, `arith` uses `rec`, `order` uses `arith`,
`finite` and `poset` use `order`, `card` uses `finite`, `ordinal` uses `poset`
and `finite`, and `trec` and `sim` use `poset` (`sim` also uses `finite`);
`ordset` for sets of ordinal numbers (Halmos §20) uses `ordinal` and `sim`;
`count` for the counting theorem (Halmos §20) uses `ordset`; `oarith` for
ordinal addition (Halmos §21) uses `count`; `omul` for ordinal multiplication
and `osub` for subtraction (Halmos §21) use `oarith`; `orec` for transfinite
recursion on the ordinals without a codomain uses `trec` and `ordset`; `opow`
for exponentiation (Halmos §21) uses `omul` and `orec`. Only `ordinal`,
`ordset`, `count`, `oarith`, `omul`, `osub`, `orec`, `opow`, `countable`,
`cardarith`, and `cardinal` may use Replacement and definite description.
`choice` adds Halmos' axiom of choice (§15) and `zorn` proves Zorn's lemma from
it (§16), using `fun` and `poset`; `wellord` proves the well ordering theorem
(§17) from Zorn's towers. `countable` (Halmos §23) and `cardarith` (Halmos §24,
cardinal arithmetic up to equivalence and Cantor's theorem) use `omul` and
Replacement but no choice. `cardinal` (Halmos §23-25) uses choice for the
countable union theorem, infinite sets containing ω, and cardinal numbers
`card(X)` with the comparability of any two sets. Only `choice`, `zorn`,
`wellord`, and `cardinal` may use choice.
"""
