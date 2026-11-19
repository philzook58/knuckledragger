"""Execute each SBV port, including its top-level proof checks, in isolation."""

import os
from pathlib import Path
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]


@pytest.mark.parametrize(
    "example", sorted((ROOT / "examples/sbv").glob("*.py")), ids=lambda p: p.stem
)
def test_sbv_example(example: Path):
    result = subprocess.run(
        [sys.executable, str(example)],
        cwd=ROOT,
        env={**os.environ, "PYTHONPATH": str(ROOT / "src")},
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert result.returncode == 0, result.stdout + result.stderr
