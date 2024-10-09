import pytest
import importlib

"""
@pytest.mark.benchmark(min_rounds=1, max_time=1)
@pytest.mark.parametrize(
    "module_name",
    [
        # "kdrag",
        "kdrag.theories.real",
        "kdrag.theories.nat",
        # "kdrag.solvers",
    ],
)
def test_import_benchmark(module_name, benchmark):
    # Benchmark the import time of the module
    module = importlib.import_module(module_name)
    importlib.invalidate_caches()
    benchmark(lambda: importlib.reload(module))
"""
