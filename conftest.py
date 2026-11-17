import os

# Tests check proofs, so they solve every query. `kdrag.all` turns the proof cache on unless KDRAG_CACHE=0,
# and pytest imports it while collecting doctests.
os.environ.setdefault("KDRAG_CACHE", "0")
