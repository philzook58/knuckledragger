"""
Explain a failed proof and suggest a verified change to `by=`.
"""

import os
import time

import kdrag.config as config
import kdrag.kernel as kernel
from kdrag.printers.pretty import pretty_goal
import kdrag.smt as smt
import kdrag.utils as utils


def _name(pf: kernel.Proof) -> str:
    """How a `by=` list would refer to `pf`: its library name, else its statement."""
    for name, q in utils.lemma_db().items():
        if q.thm.eq(pf.thm):
            return name.removeprefix("kdrag.theories.").removeprefix("__main__.")
    s = " ".join(str(pf.thm).split())
    return s if len(s) <= 40 else s[:37] + "..."


def repair(
    thm: smt.BoolRef,
    by: list[kernel.Proof],
    countermodel=False,
    timeout=50,
    budget=0.2,
    *,
    solver=None,
) -> list[kernel.Proof] | None:
    """
    The first small change to `by` that proves `thm`, or None: add a definition, add
    a suggested lemma, or drop a lemma (extra lemmas cause timeouts, not countermodels).
    """
    have = {pf.thm.get_id() for pf in by}
    defns = [kernel.defns[d].ax for d in utils.defined_decls(thm)]
    defns = [d for d in defns if d.thm.get_id() not in have]
    tries = [by + [d] for d in defns]
    tries += [
        by + [pf]
        for _, _, pf in utils.rank_lemmas(thm)[:3]
        if pf.thm.get_id() not in have
    ]
    if not countermodel and len(by) > 1:
        tries += [[q for q in by if q is not pf] for pf in by]
    start = time.perf_counter()
    for lemmas in tries:
        if time.perf_counter() - start > budget:
            break
        try:
            kernel.prove(thm, by=lemmas, timeout=timeout, solver=solver)
            return lemmas
        except Exception:
            # A proposed lemma may be unsupported by the selected solver.
            continue
    return None


def location(filename: str, line: int, func: str) -> str:
    """` at file:line in func`, which terminals and editors make clickable."""
    if os.path.isfile(filename) and "ipykernel" not in filename:  # not a notebook cell
        rel = os.path.relpath(filename)
        return f" at {filename if rel.startswith('..') else rel}:{line} in {func}"
    return f" at line {line} in {func}"


def explain(goal, error, by=(), timeout=1000, where="", source="", *, solver=None) -> str:
    """Format a proof failure with a verified repair or ranked suggestions."""
    countermodel = not isinstance(error, TimeoutError) and len(error.args) == 3
    backend = solver if isinstance(solver, str) else getattr(solver, "__name__", "z3")
    if isinstance(error, TimeoutError):
        reason = f"timed out after {timeout}ms"
    elif countermodel:
        reason = f"{backend} found a countermodel"
    else:
        reason = f"{backend} returned {error.args[2]} (SMT-LIB: {error.args[3]})"
    call = source.split("#")[0].rstrip() or "auto"  # drop a trailing comment
    lines = [pretty_goal(goal), "", f"❌ {call} failed{where}: {reason}"]
    if config.diagnose:
        by = [by] if isinstance(by, kernel.Proof) else list(by or [])
        thm = goal.to_expr()
        fix = repair(thm, by, countermodel, solver=solver)
        if fix is not None:
            lines.append(f"✅ passes with by=[{', '.join(_name(pf) for pf in fix)}]")
        else:
            suggestions = utils.suggest(thm, check=0)
            if suggestions:
                lines.append(suggestions)
    return "\n".join(lines)
