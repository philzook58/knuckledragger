"""Exploratory ZF set theory awaiting manual review and promotion to theories.

Builds on `kdrag.theories.zf.zf`, following Halmos' Naive Set Theory.

Modules: `nat` for the von Neumann naturals, ω, and the Peano axioms
(Halmos §11-12); `fun` for functions as sets of pairs (Halmos §8); `rec` for
the recursion theorem on ω (Halmos §12). Dependencies flow one way:
`nat` and `fun` are independent, and `rec` uses both.
"""
