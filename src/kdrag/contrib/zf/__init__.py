"""Exploratory ZF set theory awaiting manual review and promotion to theories.

Builds on `kdrag.theories.zf.zf`, following Halmos' Naive Set Theory.

Modules: `nat` for the von Neumann naturals, ω, and the Peano axioms
(Halmos §11-12); `fun` for functions as sets of pairs (Halmos §8); `rec` for
the recursion theorem on ω (Halmos §12); `arith` for addition and
multiplication defined by recursion (Halmos §13); `order` for the order on ω,
where `m < n` is `m ∈ n` (Halmos §13); `finite` for equivalent and finite
sets via HOL-function bijections (Halmos §13); `card` for comparing sizes and
the Schröder-Bernstein theorem (Halmos §22). Dependencies flow one way: `nat`
and `fun` are independent, `rec` uses both, `arith` uses `rec`, `order` uses
`arith`, `finite` uses `order`, and `card` uses `finite`.
"""
