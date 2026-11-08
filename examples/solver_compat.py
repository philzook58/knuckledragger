"""Replay existing Z3 proof obligations with other backends.

Run ``python examples/solver_compat.py > results.jsonl``. Each result records the
source location, backend, status, timing, and diagnostic output. The theory
imports are checked normally before their obligations are replayed.
"""

import argparse
from collections import defaultdict
import contextlib
import importlib
import inspect
import io
import json
import sys
import time
import tempfile
from pathlib import Path
from unittest.mock import patch

from kdrag import Proof
import kdrag.kernel as kernel
from kdrag.smt import Not
from kdrag.solvers import CVC5Solver, EProverSolver, EProverTHFSolver, VampireSolver


THEORIES = (
    "int",
    "real",
    "algebra.group",
    "algebra.kleene",
    "nat",
    "real.vec3",
    "real.seq",
    "regex",
    "bitvec",
    "set",
    "seq",
    "real.fun",
    "algebra.sqmatrix",
    "logic.temporal",
)
BACKENDS = {
    "cvc5": CVC5Solver,
    "vampire": VampireSolver,
    "eprover": EProverSolver,
    "eprover-ho": EProverTHFSolver,
}


def obligations():
    original = kernel.prove
    signature = inspect.signature(original)
    recorded = defaultdict(list)

    def capture(*args, **kwargs):
        bound = signature.bind(*args, **kwargs)
        bound.apply_defaults()
        values = bound.arguments
        by = values["by"]
        values["by"] = [by] if isinstance(by, Proof) else list(by)
        pf = original(**values)
        if not values["admit"] and values["solver"] is None:
            frame = sys._getframe(1)
            while frame and frame.f_globals.get("__name__") in (
                "kdrag.tactics",
                "kdrag.kernel",
            ):
                frame = frame.f_back
            if frame:
                module = frame.f_globals.get("__name__", "")
                recorded[module].append((frame.f_lineno, values["thm"], values["by"]))
        return pf

    with patch.object(kernel, "prove", capture), contextlib.redirect_stdout(sys.stderr):
        for name in THEORIES:
            importlib.import_module("kdrag.theories." + name)
    return recorded


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--timeout", type=int, default=500, help="milliseconds per attempt"
    )
    parser.add_argument("--backend", choices=BACKENDS, action="append")
    args = parser.parse_args()
    for module, cases in obligations().items():
        if module.removeprefix("kdrag.theories.") not in THEORIES:
            continue
        # Sample across the file, including the final proof obligation.
        for index in sorted({0, len(cases) // 3, 2 * len(cases) // 3, len(cases) - 1}):
            line, thm, by = cases[index]
            for backend in args.backend or BACKENDS:
                solver = None
                start = time.perf_counter()
                result = {
                    "module": module,
                    "line": line,
                    "index": index,
                    "backend": backend,
                }
                try:
                    solver = BACKENDS[backend]()
                    solver.set("timeout", args.timeout)
                    for premise in by:
                        solver.add(premise.thm)
                    solver.add(Not(thm))
                    result["status"] = str(solver.check())
                except Exception as error:
                    result.update(status="error", error=str(error))
                result["seconds"] = round(time.perf_counter() - start, 4)
                if solver is not None:
                    if solver.res is not None:
                        result["stdout"] = solver.res.stdout.decode(errors="replace")
                        result["stderr"] = solver.res.stderr.decode(errors="replace")
                    try:
                        if backend.startswith("eprover"):
                            with tempfile.TemporaryDirectory() as directory:
                                path = Path(directory) / "problem.p"
                                solver.write_tptp(path, format=solver.options["format"])
                                result["input"] = path.read_text()
                        else:
                            problem = io.StringIO()
                            solver.write_smt(problem)
                            result["input"] = problem.getvalue()
                    except Exception:
                        pass
                print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
