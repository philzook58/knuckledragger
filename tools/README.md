# Timing and Profiling Tools

This directory contains tools for analyzing test performance and proof timing in knuckledragger.

## Overview

The timing infrastructure consists of:
1. **Pytest timing plugin** (`tests/conftest.py`) - Automatically collects timing data during test runs
2. **Timing report generator** (`timing_report.py`) - Formats timing data for CI and local use
3. **Profiling tool** (`profile_tests.py`) - Generates detailed cProfile data for performance analysis

## Quick Start

### Basic Timing Reports

Run tests normally - timing data is automatically collected:

```bash
pytest tests/
```

After the test run, view the timing report:

```bash
# GitHub Actions markdown format (nice tables)
python tools/timing_report.py --format=github

# Plain text format
python tools/timing_report.py --format=plain
```

The timing report shows:
- Session duration and summary statistics
- Top 10 slowest tests
- Top 15 slowest proof operations
- Test module statistics (tests per module, total/average time)

### Profiling with cProfile

For detailed function-level profiling:

```bash
# Profile all tests
python tools/profile_tests.py

# Profile specific tests
python tools/profile_tests.py tests/test_kernel.py
python tools/profile_tests.py -k test_Lemma

# View interactive profile data
python -m pstats .pytest_profile.prof
```

The profiling tool generates:
- `.pytest_profile.prof` - Raw profile data (for interactive analysis)
- `.pytest_profile.txt` - Detailed text report
- Console output with top 20 functions by cumulative and internal time

## CI Integration

The timing report automatically runs in GitHub Actions and appears in the job summary.

In `.github/workflows/python-package.yml`:

```yaml
- name: Test with pytest
  run: uv run python -m pytest -v --tb=short

- name: Generate timing report
  if: always()
  run: uv run python tools/timing_report.py --format=github >> $GITHUB_STEP_SUMMARY

- name: Upload timing report
  if: always()
  uses: actions/upload-artifact@v4
  with:
    name: timing-report
    path: .pytest_timing_report.json
```

The timing report is visible in:
1. **GitHub Actions job summary** - Formatted markdown tables
2. **Artifacts** - Download the JSON file for further analysis

## Understanding the Output

### Test Timing

Tests are timed from setup through teardown. The report shows:
- Individual test duration
- Module aggregates (total and average time per test file)

Example:
```
1.  2.8686s  tests/test_solver.py::test_huet
2.  0.0943s  tests/test_solver.py::test_vampirethf
3.  0.0779s  tests/test_solver.py::test_huet_smt
```

### Proof Operation Timing

When `config.timing = True` (automatically set by the plugin), proof operations are logged with:
- **Category**: `Calc`, `ProofState`, `prove`, etc.
- **Duration**: Time spent in Z3
- **Description**: The theorem or goal being proved

Example:
```
1.   0.0185s [Calc           ] |= ForAll(x, mul(x, inv(x)) == e)
2.   0.0180s [ProofState     ] [] ?|= ForAll([x, y], add(x, S(y)) == S(add(x, y)))
```

Categories:
- **`prove`** - Direct calls to `kd.prove()`
- **`ProofState`** - Tactic-based proofs using `Lemma` or `@Theorem`
- **`Calc`** - Equational reasoning chains

### Module Statistics

Shows aggregated data per test module:
```
| Module              | Tests | Total Time | Avg Time |
|---------------------|-------|------------|----------|
| tests/test_solver.py| 15    | 3.524s     | 0.2349s  |
| tests/test_kernel.py| 21    | 0.077s     | 0.0037s  |
```

## Interpreting Results

### What to look for:

1. **Slow tests** - Tests taking >1s may benefit from optimization or marking as `@pytest.mark.slow`

2. **Slow proof operations** - Proofs taking >0.01s indicate:
   - Complex theorems requiring more Z3 effort
   - Possible need for lemma breaking
   - Candidates for timeout increases

3. **Module imbalances** - If one module is much slower on average:
   - Tests may need better isolation
   - Consider splitting into faster sub-modules
   - Mark slow integration tests appropriately

### Common patterns:

- **Proof timeouts**: If proofs fail with timeout, the timing report shows which operations are close to limits
- **CI slowness**: Module statistics help identify which test files dominate CI time
- **Proof instability**: Running tests multiple times and comparing timing reports can detect inconsistent proof times

## Advanced Usage

### Custom timing in your code

The timing infrastructure is available for custom instrumentation:

```python
import kdrag.config as config

# Enable timing
config.timing = True

# Your timing data will be collected automatically
# All calls to prove(), ProofState methods, and Calc operations are timed

# Access timing data
for tag, data, duration in config.perf_log:
    print(f"{tag}: {duration:.4f}s - {data}")
```

### Analyzing specific proofs

To focus on specific slow proofs:

```bash
# Run just the slow test
pytest tests/test_solver.py::test_huet -v

# View proof timings
python tools/timing_report.py --format=plain | grep -A 20 "SLOWEST PROOF"
```

### Comparing timing between runs

```bash
# Run tests and save report
pytest tests/
cp .pytest_timing_report.json timing_before.json

# Make changes...

# Run again and compare
pytest tests/
python tools/timing_report.py --format=plain > timing_after.txt
```

## Files Generated

These files are generated during test runs and are excluded from git:

- `.pytest_timing_report.json` - JSON report with all timing data
- `.pytest_profile.prof` - cProfile binary data (from profile_tests.py)
- `.pytest_profile.txt` - Text profiling report (from profile_tests.py)

## See Also

- `tests/perf.py` - Module import timing script
- `src/kdrag/config.py` - Configuration including timing flag
- Original issue: [Make CI to check and record time for proofs](https://github.com/philzook58/knuckledragger/issues/XXX)
