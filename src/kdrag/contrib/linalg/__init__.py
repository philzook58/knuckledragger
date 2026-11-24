"""Exploratory linear algebra after Axler's *Linear Algebra Done Right*, kept
concrete: vectors are `RSeq = Int -> Real`, lists of vectors are families
`Int -> RSeq` with a length, and subspaces are sets `RSeq -> Bool`.

Modules, in dependency order: `span` (linear combinations, span),
`indep` (linear independence), `dim` (independent length <= spanning length).
"""
