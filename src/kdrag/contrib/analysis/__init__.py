"""Exploratory real analysis awaiting manual review and promotion to theories.

Modules: `cont` for limits and continuity, `deriv` for differentiation,
`rseq` for sequence limits, `finsum` for finite sums, `integral` for the gauge
integral, and `ftc` for the fundamental theorem. `_choice` supplies pointwise
choice for gauges. Dependencies flow from these foundations towards `ftc`.

Load the reviewed sequence and continuity foundations before exploratory proofs
so their proof imports do not depend on the first exploratory module requested.
"""

from kdrag.theories.real import rseq as _reviewed_rseq  # noqa: F401
from kdrag.theories.real import cont as _reviewed_cont  # noqa: F401
