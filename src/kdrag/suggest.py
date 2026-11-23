"""
Suggest library lemmas likely to help prove a goal, ranked by tf-idf cosine of their
function symbols (as in Sledgehammer's MePo and SInE).
"""

import math
import time
from collections import Counter

import kdrag.kernel as kernel
import kdrag.smt as smt
import kdrag.utils as utils

BUILTIN = 0.1  # weight of built-ins (+, =, and, ...) relative to user symbols

_decls: dict[int, Counter[smt.FuncDeclRef]] = {}  # cache, by `thm.get_id()`


def decl_counter(e: smt.ExprRef) -> Counter[smt.FuncDeclRef]:
    """Function symbols in `e`, skipping fresh variables like x!7."""
    return Counter(
        t.decl()
        for t in utils.subterms(e, into_binder=True)
        if smt.is_app(t) and "!" not in t.decl().name()
    )


def lemmas() -> dict[int, tuple[str, kernel.Proof]]:
    """Public lemmas and definitions from `utils.lemma_db`, by `thm.get_id()`."""
    out = {}
    # __main__ last, so a star-imported lemma keeps its defining module's name.
    for name, pf in sorted(
        utils.lemma_db().items(), key=lambda kv: kv[0].startswith("__main__.")
    ):
        if not name.rsplit(".", 1)[-1].startswith("_"):
            out.setdefault(pf.thm.get_id(), (name, pf))
    return out


def rank(thm: smt.BoolRef) -> list[tuple[float, str, kernel.Proof]]:
    """Every library lemma as `(score, name, proof)`, best first for proving `thm`."""
    db = lemmas()
    decls = {}
    for key, (_, pf) in db.items():
        if key not in _decls:
            _decls[key] = decl_counter(pf.thm)
        decls[key] = _decls[key]
    df = Counter(d for c in decls.values() for d in c)

    def tfidf(c: Counter) -> dict[smt.FuncDeclRef, float]:
        return {
            d: (1.0 if smt.is_uninterp(d) else BUILTIN)
            * (1 + math.log(n))
            * math.log(len(db) / df.get(d, 1))
            for d, n in c.items()
        }

    goal = tfidf(decl_counter(thm))
    scored = []
    for key, (name, pf) in db.items():
        v = tfidf(decls[key])
        norm = math.sqrt(sum(x * x for x in v.values())) or 1.0
        scored.append(
            (sum(x * v.get(d, 0.0) for d, x in goal.items()) / norm, name, pf)
        )
    scored.sort(key=lambda t: -t[0])
    return scored


def report(thm: smt.BoolRef, k=10, cutoff=0.5, check=3, timeout=30, budget=0.1) -> str:
    """
    The top `k` suggestions for `thm` scoring at least `cutoff` times the best. The
    first `check` are tried with z3 within `budget` seconds; ✅ marks one that proves
    `thm` on its own.
    """
    from kdrag.printers.pretty import pretty_expr

    ranked = rank(thm)[:k]
    start = time.perf_counter()
    lines = []
    for i, (score, name, pf) in enumerate(ranked):
        if score < cutoff * ranked[0][0]:
            break
        mark = "- "  # two columns, like the emoji
        if i < check and time.perf_counter() - start < budget:
            try:
                kernel.prove(thm, by=[pf], timeout=timeout)
                mark = "✅"
            except Exception:
                pass
        stmt = " ".join(pretty_expr(pf.thm).split())
        if len(stmt) > 70:
            stmt = stmt[:67] + "..."
        lines.append(f"  {mark} {name.removeprefix('kdrag.theories.')}: {stmt}")
    return "Suggestions:\n" + "\n".join(lines) if lines else ""
