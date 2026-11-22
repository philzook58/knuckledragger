# Knuckledragger in JupyterLite

A JupyterLite site where z3 and knuckledragger run in the browser via Pyodide.

```
pip install -r lite/requirements.txt
lite/build.sh                      # bundles the local kdrag wheel + z3 Pyodide wheel
python -m http.server -d lite/_output 8765
```

Open `http://127.0.0.1:8765/lab/index.html?path=reals.ipynb`.

Versions are pinned to line up: `jupyterlite-pyodide-kernel` 0.8.7 loads Pyodide 314.0.6
(CPython 3.14, ABI `pyemscripten_2026_0`), matching
`z3_solver-5.3.3.0-py3-none-pyemscripten_2026_0_wasm32.whl` from PyPI. z3 5.4.x has no Pyodide wheel.

## "try" links in the docs

With `KDRAG_LITE_URL` set, the theorem index (`docs/theorem_index.py`) adds a JupyterLite icon per theorem.
It opens the REPL with the theorem's proof source in an editable prompt. The code travels in the URL,
at most about 3.6 KB, so no per-theorem files are generated. Shift+Enter runs it, and the code stays in the prompt
for editing. In `@Theorem` proofs (77 of the 248 real theorems), the decorator becomes `@PTheorem` and an early
`return` goes before the first tactic. Running the cell shows the starting goal. Moving the `return` down (Alt+Down)
and rerunning steps through the proof. Other theorems, mostly one-line `prove(...)` calls, are shown as-is.
Cell code comes from `docs/lite_cells.py`. Theorems listed in `docs/lite_skip.txt` get no link. Regenerate that file
under Pyodide with `node tools/pyodide_smoke.mjs lite/pypi/knuckledragger-*.whl tools/check_lite_cells.py --write`,
which takes about 13s. The check runs every cell, plus each stepping proof fully uncommented. As of 2026-11-21,
566 of 569 cells work. The three exceptions:
- `real.arb` needs `python-flint`.
- `float.minfloat` and `real.measure.omu_interval` use a variable that their module later rebinds to another sort,
  so a star import can't replay them.

The cell does `from kdrag.all import *`, then `from <module> import *`. It installs with `--no-deps`
to skip sympy, about 6.5 MB. All 248 real theorems reprove from their link code.

Warm cache: kernel boot 4.7s, then the first run takes 3.6s (install 0.6s, imports and the proof ~3s), and reruns ~0.1s.
A cold load also downloads about 25 MB: Pyodide ~13 MB from the jsdelivr CDN, z3 6.7 MB, and the JupyterLite JS.
The z3 wheel ships `libz3.so` twice, so about 3 MB of that could be dropped by repacking it.

```
KDRAG_LITE_URL=lite sphinx-build docs _build
lite/build.sh $PWD/_build/lite        # after sphinx: the docs build downloads solvers into src/
python -m http.server -d _build 8765  # then open /theorems.html
```

## Headless check

```
npm install pyodide@314.0.6
node tools/pyodide_smoke.mjs dist/knuckledragger-*.whl   # runs tools/real_smoke.py
```

## Results (2026-11-21)

Import times from `tools/real_smoke.py`. Each row is incremental, since every module imports the ones above it.

| module | native py3.14 | Pyodide (Node) |
|---|---|---|
| `kdrag` | 0.42s | 1.22s |
| `kdrag.theories.real` | 0.17s | 0.51s |
| `kdrag.theories.real.rseq` | 0.72s | 1.60s |
| `kdrag.theories.real.rset` | 0.00s | 0.00s |
| `kdrag.theories.real.cont` | 0.17s | 0.39s |
| `kdrag.theories.real.analysis` | 0.08s | 0.14s |
| **total** | 1.56s | 3.86s |

- In the browser, the demo notebook's import cell (`kdrag`, `real`, `rseq`) took 3.0s. Every cell ran.
- `tests/test_real*.py` and `tests/test_rseq.py` under Pyodide: 12/12 runnable tests pass. Excluded: the
  `python-flint` test (no Pyodide build of flint) and the two `subprocess` tests (no process spawning).
- The real-module doctests (excluding `arb.py`) pass 6/6, taking 4.6s vs 1.6s natively.
- No wasm-only proof failures were found. Solver work is about 3× slower: the same `rlimit` run takes 0.52s vs 0.18s.

## Known issues

- **z3 `timeout` never fires on nonlinear integer goals under Pyodide.** In the native build,
  `a**3 + b**3 + c**3 == 33` with `timeout=1000` returns `unknown` after 1s. Under Pyodide it spins
  forever. `rlimit` still works. Timeouts do fire for quantifier search (E-matching loops, MBQI),
  which is the usual way a kdrag proof fails, but the reason given is `canceled`, not `timeout`. The cause is likely
  the `POLLING_TIMER` build: the deadline is set on the root `reslimit`, but the arithmetic solver
  polls child limits. `kernel.prove` works around this: under emscripten it also sets
  `rlimit = timeout * 10_000`, about 2.5x the timeout there. With `timeout=1000`, that goal raises
  `TimeoutError` after 1.8s.
- `kdrag.theories.real.arb` needs `python-flint`, which Pyodide does not ship.
- A runaway z3 call made outside `kd.prove`, for example on a raw `smt.Solver` without an rlimit, can't be interrupted. Restart the kernel.
