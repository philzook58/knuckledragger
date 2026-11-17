"""
Check that the proof cache speeds up importing `kdrag.all` and the theories.
Run as `python tests/cache_check.py`. It imports them twice, in fresh processes sharing an empty cache directory.
"""

import os
import subprocess
import sys
import tempfile

IMPORT_ALL = """
import importlib, pkgutil, time
start = time.perf_counter()
import kdrag.all
import kdrag.proof_cache as pc
import kdrag.theories as thy
for m in pkgutil.walk_packages(thy.__path__, "kdrag.theories."):
    if not m.ispkg and not m.name.split(".")[-1].startswith("_"):
        try:
            importlib.import_module(m.name)
        except Exception:
            pass
print(time.perf_counter() - start, pc.hits, pc.misses)
"""


def import_all(cache_dir: str) -> tuple[float, int, int]:
    """Seconds, cache hits and misses of importing everything with the cache in `cache_dir`."""
    env = dict(os.environ, KDRAG_CACHE_DIR=cache_dir)
    env.pop("KDRAG_CACHE", None)  # let kdrag.all turn the cache on
    out = subprocess.run(
        [sys.executable, "-c", IMPORT_ALL],
        env=env,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    secs, hits, misses = out.splitlines()[-1].split()
    return float(secs), int(hits), int(misses)


if __name__ == "__main__":
    with tempfile.TemporaryDirectory() as cache_dir:
        cold_secs, _, cold_misses = import_all(cache_dir)
        warm_secs, warm_hits, warm_misses = import_all(cache_dir)
    print(f"cold {cold_secs:.2f}s, {cold_misses} queries solved")
    print(f"warm {warm_secs:.2f}s, {warm_hits} cached, {warm_misses} solved")
    if warm_hits < 0.95 * (warm_hits + warm_misses):
        sys.exit("Too few proof cache hits on the second import")
    if warm_secs > 0.75 * cold_secs:
        sys.exit("The proof cache did not reduce import time")
