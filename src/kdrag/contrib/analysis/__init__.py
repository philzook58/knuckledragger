"""Exploratory real analysis awaiting manual review and promotion to theories.

Sequence limits, subsequences, and completeness live in `rseq`,
`subsequence`, and `cauchy`. Finite sums and series live in `finsum` and
`series`, with applications in `contraction` and `sine`.

Pointwise limits and continuity live in `cont`. Properties of real sets
live in `topology`, `compact`, and `connected`. The connectedness proof of
the intermediate value theorem lives in `connected`; the bisection proof
lives in `ivt`.

Derivative rules live in `deriv`, with interval theorems in `darboux` and
`mvt` and quotient limits in `lhopital`. The gauge integral lives in
`integral`, and `ftc` connects it to differentiation.

Load the reviewed sequence and continuity foundations before exploratory proofs
so their proof imports do not depend on the first exploratory module requested.
"""

from kdrag.theories.real import rseq as _reviewed_rseq  # noqa: F401
from kdrag.theories.real import cont as _reviewed_cont  # noqa: F401
