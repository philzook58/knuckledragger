# Theorem links into JupyterLite

With `KDRAG_LITE_URL` set, the theorem index (`docs/theorem_index.py`) gives each theorem a JupyterLite icon.
It opens a browser Python REPL (Pyodide) with the theorem's proof in an editable prompt. The code travels in
the URL, so no per-theorem files are generated. `@Theorem` proofs come as `@PTheorem` with an early `return`
before the first tactic. Shift+Enter shows the starting goal, and moving the `return` down (Alt+Down) steps
through the proof. Other theorems, mostly one-line `prove(...)` calls, are shown as-is.

- `cells.py` builds the cell code, which runs `from kdrag.all import *` and then `from <module> import *`.
- `build.sh` builds the site, bundling the local wheel, the z3 Pyodide wheel, lark and graphviz.
  The cell installs them with `--no-deps`, which skips sympy (about 6.5 MB).
- `check_cells.py` runs every cell under Pyodide, plus each stepping proof fully uncommented, in about 13s.
  It writes failures to `skip.txt`, and those theorems get no link. CI regenerates the file on every docs build.
- `run_pyodide.mjs` runs a Python script against a kdrag wheel under Pyodide in Node.

Versions are pinned to line up: `jupyterlite-pyodide-kernel` 0.8.7 loads Pyodide 314.0.6 (CPython 3.14, ABI
`pyemscripten_2026_0`), matching `z3_solver-5.3.3.0-py3-none-pyemscripten_2026_0_wasm32.whl`.
z3 5.4.x has no Pyodide wheel.

## Local build

From the repository root:

```
pip install -r docs/lite/requirements.txt
docs/lite/build.sh $PWD/_build/lite
npm install --no-save pyodide@314.0.6
node docs/lite/run_pyodide.mjs docs/lite/pypi/knuckledragger-*.whl docs/lite/check_cells.py --write
KDRAG_LITE_URL=lite sphinx-build docs _build
python -m http.server -d _build 8765   # then open /theorems.html
```

## Status (2026-11-21)

- 566 of 569 cells work. The three exceptions:
  - `real.arb` needs `python-flint`.
  - `float.minfloat` and `real.measure.omu_interval` use a variable that their module later rebinds to another
    sort, so a star import can't replay them.
- Pyodide is about 2.5-3× slower than native. Importing `real`, `rseq`, `rset`, `cont` and `analysis` takes 3.9s,
  vs 1.6s on CPython 3.14.
- With a warm browser cache, kernel boot takes 4.7s, the first run about 3.5s, and reruns about 0.1s.
- A cold load also downloads about 25 MB. Most of that is Pyodide (about 13 MB, from the jsdelivr CDN) and the
  z3 wheel (6.7 MB). The z3 wheel ships `libz3.so` twice.

## Known issues

- **z3 `timeout` never fires on nonlinear integer goals under Pyodide.** In the native build,
  `a**3 + b**3 + c**3 == 33` with `timeout=1000` returns `unknown` after 1s. Under Pyodide it spins forever.
  Quantifier search does time out, but reports `canceled`. The likely cause is the `POLLING_TIMER` build: the
  deadline is set on the root `reslimit`, while the arithmetic solver polls child limits. `kernel.prove` works around
  this under emscripten by also setting `rlimit = timeout * 10_000`, about 2.5× the timeout there. That goal now
  raises `TimeoutError` after 1.8s.
- A runaway z3 call outside `kd.prove`, for example on a raw `smt.Solver`, can't be interrupted. Restart the
  kernel.
