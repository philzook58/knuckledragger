# Main test investigation — 2026-11-07

Investigated `origin/main` at `176d9840f744ad8812a481b34c85e93f75070a4b`
on branch `investigate/main-test-failures`, in a separate worktree.
Existing edits in both older checkouts were preserved.

## GitHub Actions

- [Latest Python run](https://github.com/philzook58/knuckledragger/actions/runs/30022398952):
  hit the six-hour limit in **Install dependencies**, before pytest started.
- [Previous Python run](https://github.com/philzook58/knuckledragger/actions/runs/29602112011):
  pytest exited with code 2. Detailed logs have expired (HTTP 410), so its
  exact collection errors cannot be recovered.
- Both runs also failed artifact upload because `/tmp/kdrag` did not exist;
  neither reached the perf step that creates it.

## Reproduced problems and branch fixes

| Location | Failure | Change |
| --- | --- | --- |
| `theories/real/geometry.py::_is_line1` | Quantified witness proof returns `unknown`, sometimes followed by “Worked with quantifier stripped.” | Fix the shape explicitly and instantiate its defining theorem. Apply the same pattern to `_is_dir1`. |
| `theories/algebra/kleene.py::star_star` | Vampire search sometimes exceeds its five-second timeout during collection. | Derive `star_incl`, then prove `star_seq_star` and `star_star` through induction, monotonicity, and explicit axiom instances with Z3. |
| `kernel.py::choose` | Passes alone but sometimes rejects its closed doctest theorem after other tests run. Z3 reuses collected schema-variable IDs for newly opened binders. | Check the original quantified theorem for free schema variables before opening binders. Add collection/reuse and free-variable rejection tests. |
| `contrib/fast/__init__.py` | Generated CFFI wrappers lack C declarations; their opaque Z3 struct names also disagree with the headers. Compilation failure leaves the process in a temporary directory, causing secondary notebook/README path failures. | Compile the C implementation in the wrapper translation unit, use the header's struct names, and pass `tmpdir` directly instead of changing directory. |
| `solvers/tla.py` | `tla2tools.jar` fails checksum validation, blocking collection. | Update the checksum to the release asset's independently verified GitHub digest. |
| `hypothesis.py::smt_generic_val` | Randomly generated sorts can block inside model enumeration for over 60 seconds; stack dump points to `s.check()`. | Add a configurable 100 ms timeout per solver call. Reject an initially unknown draw; otherwise retain the last value from a satisfiable model. |

The [TLA+ v1.8.0 asset](https://github.com/tlaplus/tlaplus/releases/tag/v1.8.0)
was updated on **2026-11-06**. GitHub's release API reports SHA-256
`e1f11b75c4b5bc4478ba0ac5cb6ae28e40a01b0016bc33e0aa97da22dfdbcd7f`,
matching the downloaded jar. This newly observed checksum failure cannot explain
the historical July CI failures.

## Validation and environment

- Python 3.12.12, locked dependencies including Z3 4.15.4 and pytest 8.3.4.
- Ran the CI test selection, including slow tests: `python -m pytest -m ''`.
  After the kernel fix, **607 passed** in 158.78 seconds. This run exposed the
  model-generation stall subsequently bounded by the timeout change.
- Final run including the timeout change: **607 passed** in **74.44 seconds**.
- Geometry and Kleene imports passed ten fresh-process runs with varied solver
  seeds and preceding symbol allocations. Geometry: 0.269–0.346 s including
  dependencies; Kleene: 0.029–0.042 s.
- Ruff and `git diff --check` pass. `python tests/perf.py` completes with no
  import failures; incremental geometry/Kleene imports were 0.055/0.023 s.
- Notebook kernels need local sockets and RISC-V assembly tests need Nix;
  the full run used the host environment with `.venv/bin` on `PATH` and
  `VIRTUAL_ENV` set. Sandboxed failures here were environmental.
- Reused installed solver binaries from the sibling checkout rather than rerun
  the unbounded installation script. Added `pip` to this worktree's venv because
  `maturin develop` needs it; a fresh uv venv does not supply it. These setup
  changes do not modify the lockfile.
- An initial `test_val_of_sort` run failed Hypothesis's slow-generation health
  check; subsequent runs passed. Its recursive structural generator remains a
  separate potential source of timing variability.

## Remaining CI issues

- The solver installer timeout is separate from proofs. Its expired logs do not
  identify the stalled command. Downloads in `install.sh` have no explicit time
  bounds; bounding them and the installation step would improve diagnosis.
- `uvx ty check` reports **21 errors and six warnings**, identically on a clean
  main snapshot and this branch: 13 missing `scryer.Term` attributes, five
  insufficiently narrowed TLA array expressions, three missing `flint.arb`
  attributes, and six unused suppressions. These remain unchanged.

## Z3 upgrade for the pull request

- Raised the minimum Z3 version to 5.3.3 and updated only `z3-solver` in the
  lockfile, from 4.15.4.0 to [5.3.3.0](https://pypi.org/project/z3-solver/5.3.3.0/),
  the latest stable PyPI release checked on 2026-11-07.
- The newer solver exposed timeouts in `real.seq.cumsum_add` and
  `abs_le_finsum_abs`. The addition proof now unfolds the outer recurrence
  without expanding its sequence arguments; `finsum_succ` provides a pointwise
  recurrence shared by both absolute-sum induction cases.
- The sequence module passed five fresh-process runs with varied solver seeds;
  its slowest individual proof took 0.020–0.030 seconds.
- Validation with the upgraded solver: **606 passed, one failed** in 76.91 s.
  `regex.ReSort` fails while constructing `star_unfold`: the new solver returns
  `unknown` for the generic identity `1 + r * star(r) = star(r)`. The symmetric
  identity also returns `unknown` in isolation. This is a separate backend
  regression from the sequence timeouts, and remains unresolved pending the
  user's decision about explicit regex axioms.
- Ruff passes; perf completes with no import failures; ty has the same 21
  errors and six warnings. The pull request remains a draft while the regex
  regression is unresolved.
