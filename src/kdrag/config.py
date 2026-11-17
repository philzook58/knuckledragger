"""
Global configuration of Knuckledragger
"""

import os

solver = None
cache: bool = os.environ.get("KDRAG_CACHE") == "1"
"""Reuse z3 results from earlier runs (see `kdrag.proof_cache`). `kdrag.all` turns it on unless KDRAG_CACHE=0. Set KDRAG_CACHE=1 before import to also cover kdrag's own proofs."""
cache_dir: str = os.environ.get("KDRAG_CACHE_DIR") or os.path.join(
    os.environ.get("XDG_CACHE_HOME") or os.path.expanduser("~/.cache"), "kdrag"
)
admit_enabled = True
# timeout = 1000
admit_level = 50
strict_define: bool = True

# TODO: Someday, when it is annoyingly slow to check built in theories, we can add a flag to disable them
# check_lib = True
timing = False
perf_log = []


def perf_event(tag, data, time):
    if timing:
        perf_log.append((tag, data, time))
