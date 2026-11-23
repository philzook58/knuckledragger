"""Exploratory real analysis awaiting manual review and promotion to theories.

Load the shared reviewed sequence and continuity foundations before exploratory proofs, so its
proof imports do not depend on which exploratory module was requested first.
"""

from kdrag.theories.real import rseq as _reviewed_rseq  # noqa: F401
from kdrag.theories.real import cont as _reviewed_cont  # noqa: F401
