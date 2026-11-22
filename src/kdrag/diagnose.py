"""
Explain why `auto` failed: the reason, the goal, and a `by=` change that makes it pass.

Only runs when a failure is shown, never on the proving path, and calls only
`kernel.prove`, so it adds nothing to the trusted core.
"""

import time

import kdrag.config as config
import kdrag.kernel as kernel
import kdrag.smt as smt
import kdrag.suggest as suggest


def _name(pf: kernel.Proof) -> str:
    suggest.index.refresh()
    entry = suggest.index.entries.get(pf.thm.get_id())
    if entry is not None:
        return entry.name.removeprefix("kdrag.theories.")
    s = " ".join(str(pf.thm).split())
    return s if len(s) <= 40 else s[:37] + "..."


def _defns(thm: smt.BoolRef) -> list[kernel.Proof]:
    """Definitions of the defined symbols in `thm`."""
    seen, out, todo = set(), [], [thm]
    while todo:
        t = todo.pop()
        if t.get_id() in seen:
            continue
        seen.add(t.get_id())
        if isinstance(t, smt.QuantifierRef):
            todo.append(t.body())
        elif smt.is_app(t):
            if t.decl() in kernel.defns:
                out.append(kernel.defns[t.decl()].ax)
            todo.extend(t.children())
    return list({pf.thm.get_id(): pf for pf in out}.values())


def repair(
    thm: smt.BoolRef,
    by: list[kernel.Proof],
    countermodel=False,
    timeout=50,
    budget=0.2,
) -> str | None:
    """
    The first small change to `by` that proves `thm`, as text, or None.

    Tries adding a missing definition, then a suggested lemma, then dropping a
    lemma (an extra lemma can cause a timeout, but never a countermodel). Each try
    gets `timeout` ms. On failures from the existing proofs, 50ms tries in a 0.2s
    budget found as many fixes as 200ms in 0.5s (see tools/lemma_suggest).
    """
    have = {pf.thm.get_id() for pf in by}
    defns = [d for d in _defns(thm) if d.thm.get_id() not in have]
    tries = [(f"adding {_name(d)}", by + [d]) for d in defns]
    if len(defns) > 1:
        tries.append(("adding " + ", ".join(_name(d) for d in defns), by + defns))
    tries += [
        (f"adding {s.name.removeprefix('kdrag.theories.')}", by + [s.proof])
        for s in suggest.rank(thm, k=3)
        if s.proof.thm.get_id() not in have
    ]
    if not countermodel and len(by) > 1:
        tries += [(f"without {_name(pf)}", [q for q in by if q is not pf]) for pf in by]
    start = time.perf_counter()
    for label, lemmas in tries:
        if time.perf_counter() - start > budget:
            break
        try:
            kernel.prove(thm, by=lemmas, timeout=timeout)
            return label
        except (kernel.LemmaError, TimeoutError):
            pass
    return None


def explain(goal, error, by=(), timeout=1000, where="", source="") -> str:
    """
    Text for a failed `auto` on `goal` (a `tactics.Goal`).

    `where` and `source` locate the failing call, as `PTheorem` reports it.
    """
    from kdrag.printers.pretty import pretty_goal

    countermodel = not isinstance(error, TimeoutError) and len(error.args) == 3
    if isinstance(error, TimeoutError):
        reason = f"timed out after {timeout}ms"
    elif countermodel:
        # The model uses fresh names (x!7) that don't match the printed goal.
        reason = "z3 found a countermodel"
    else:
        reason = f"z3 returned {error.args[2]} (SMT-LIB: {error.args[3]})"
    # Goal first, since it's what you read; then what failed and any repair.
    # Emoji rather than ANSI color: they survive Jupyter, logs and copy-paste.
    lines = [pretty_goal(goal), "", f"❌ {source or 'auto'} failed{where}: {reason}"]
    if config.diagnose:
        if isinstance(by, kernel.Proof):
            by = [by]
        fix = repair(goal.to_expr(), list(by or []), countermodel)
        if fix is not None:
            lines.append(f"✅ passes {fix}")
    return "\n".join(lines)
