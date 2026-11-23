"""
Explain a failed `auto`: the goal, why it failed, and a `by=` change that makes it pass.
"""

import os
import time

import kdrag.config as config
import kdrag.kernel as kernel
import kdrag.smt as smt
import kdrag.suggest as suggest
import kdrag.utils as utils


def _name(pf: kernel.Proof) -> str:
    """How a `by=` list would refer to `pf`: its library name, else its statement."""
    for name, q in utils.lemma_db().items():
        if q.thm.eq(pf.thm):
            return name.removeprefix("kdrag.theories.").removeprefix("__main__.")
    s = " ".join(str(pf.thm).split())
    return s if len(s) <= 40 else s[:37] + "..."


def repair(
    thm: smt.BoolRef, by: list[kernel.Proof], countermodel=False, timeout=50, budget=0.2
) -> list[kernel.Proof] | None:
    """
    The first small change to `by` that proves `thm`, or None: add a definition, add
    a suggested lemma, or drop a lemma (extra lemmas cause timeouts, not countermodels).
    """
    have = {pf.thm.get_id() for pf in by}
    defns = [kernel.defns[d].ax for d in utils.defined_decls(thm)]
    defns = [d for d in defns if d.thm.get_id() not in have]
    tries = [by + [d] for d in defns]
    if len(defns) > 1:
        tries.append(by + defns)
    tries += [
        by + [pf]
        for _, _, pf in suggest.rank_lemmas(thm)[:3]
        if pf.thm.get_id() not in have
    ]
    if not countermodel and len(by) > 1:
        tries += [[q for q in by if q is not pf] for pf in by]
    start = time.perf_counter()
    for lemmas in tries:
        if time.perf_counter() - start > budget:
            break
        try:
            kernel.prove(thm, by=lemmas, timeout=timeout)
            return lemmas
        except (kernel.LemmaError, TimeoutError):
            pass
    return None


def location(filename: str, line: int, func: str) -> str:
    """` at file:line in func`, which terminals and editors make clickable."""
    if os.path.isfile(filename) and "ipykernel" not in filename:  # not a notebook cell
        rel = os.path.relpath(filename)
        return f" at {filename if rel.startswith('..') else rel}:{line} in {func}"
    return f" at line {line} in {func}"


def explain(goal, error, by=(), timeout=1000, where="", source="") -> str:
    """Text for a failed `auto` on `goal`; `where` and `source` locate the call."""
    from kdrag.printers.pretty import pretty_goal

    countermodel = not isinstance(error, TimeoutError) and len(error.args) == 3
    if isinstance(error, TimeoutError):
        reason = f"timed out after {timeout}ms"
    elif countermodel:  # not shown: its fresh names (x!7) don't match the goal
        reason = "z3 found a countermodel"
    else:
        reason = f"z3 returned {error.args[2]} (SMT-LIB: {error.args[3]})"
    call = source.split("#")[0].rstrip() or "auto"  # drop a trailing comment
    lines = [pretty_goal(goal), "", f"❌ {call} failed{where}: {reason}"]
    if config.diagnose:
        by = [by] if isinstance(by, kernel.Proof) else list(by or [])
        fix = repair(goal.to_expr(), by, countermodel)
        if fix is not None:
            lines.append(f"✅ passes with by=[{', '.join(_name(pf) for pf in fix)}]")
    return "\n".join(lines)
