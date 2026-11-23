"""
Suggest library lemmas that are likely to help prove a goal.

Lemmas are ranked by shared rare symbols (tf-idf cosine, as in Sledgehammer's MePo
and SInE filters) with a small bonus for recent lemmas, then the best few are tried
with z3.

Replaying the theories' own `prove` calls (2026-11, 438 with library lemmas in `by=`,
only lemmas older than each call offered), a used lemma was in the top 10 for 92%
of calls. k-NN over earlier calls (MaSh-style) and scikit-learn learned rankers did
not beat this on held-out modules with so little data, so they were left out.
"""

import math
import time
from collections import Counter
from dataclasses import dataclass, field

import kdrag.kernel as kernel
import kdrag.smt as smt
import kdrag.tactics as tactics
import kdrag.utils as utils


def decl_counter(e: smt.ExprRef) -> Counter[smt.FuncDeclRef]:
    """Function symbols in `e`, skipping fresh variables like x!7."""
    return Counter(
        t.decl()
        for t in utils.subterms(e, into_binder=True)
        if smt.is_app(t) and "!" not in t.decl().name()
    )


# Weight of built-ins (+, =, and, ...) relative to user symbols. Measured (2026-11) on
# 437 recorded prove calls: 0 or 1 loses 2-5 points of top-10 hits; 0.1-0.3 is flat.
BUILTIN = 0.1


@dataclass(repr=False)  # the default repr would print the whole library
class Index:
    """Library lemmas and definitions found by `utils.lemma_db`, oldest first."""

    # All keyed by `thm.get_id()`, except `idf`.
    entries: dict[int, tuple[str, kernel.Proof]] = field(default_factory=dict)
    decls: dict[int, Counter[smt.FuncDeclRef]] = field(default_factory=dict)
    idf: dict[smt.FuncDeclRef, float] = field(default_factory=dict)
    vecs: dict[int, dict[smt.FuncDeclRef, float]] = field(default_factory=dict)

    def refresh(self):
        n = len(self.entries)
        # Definitions after lemmas, so they get the recency bonus as before; __main__
        # last, so a star-imported lemma keeps its defining module's name.
        db = sorted(
            utils.lemma_db().items(),
            key=lambda kv: (kv[0].endswith(".defn"), kv[0].startswith("__main__.")),
        )
        for name, pf in db:
            key = pf.thm.get_id()
            if key not in self.entries and not name.rsplit(".", 1)[-1].startswith("_"):
                self.entries[key] = (name, pf)
                self.decls[key] = decl_counter(pf.thm)
        if len(self.entries) != n:
            df = Counter(d for decls in self.decls.values() for d in decls)
            self.idf = {d: math.log(len(self.entries) / c) for d, c in df.items()}
            self.vecs = {}

    def vec(self, decls: Counter[smt.FuncDeclRef]) -> dict[smt.FuncDeclRef, float]:
        """Normalized tf-idf vector of decl counts; built-ins weighted by `BUILTIN`."""
        default = math.log(len(self.entries) + 1)
        v = {}
        for d, n in decls.items():
            w = 1.0 if smt.is_uninterp(d) else BUILTIN
            v[d] = w * (1 + math.log(n)) * self.idf.get(d, default)
        norm = math.sqrt(sum(x * x for x in v.values())) or 1.0
        return {d: x / norm for d, x in v.items()}

    def __getitem__(self, thm: smt.ExprRef) -> dict[smt.FuncDeclRef, float]:
        """tf-idf vector of an indexed theorem, cached."""
        key = thm.get_id()
        if key not in self.vecs:
            self.vecs[key] = self.vec(self.decls[key])
        return self.vecs[key]


index = Index()


HYPS = 0.3  # weight of hypothesis symbols relative to the conclusion's


def rank(goal: tactics.Goal | smt.BoolRef) -> list[tuple[float, str, kernel.Proof]]:
    """
    Every library lemma as `(score, name, proof)`, best first for proving `goal`.

    The score is the tf-idf cosine of shared symbols plus a small recency bonus.
    """
    index.refresh()
    if not index.entries:
        return []
    if isinstance(goal, smt.BoolRef):
        goal = tactics.Goal(sig=[], ctx=[], goal=goal)
    g = index.vec(decl_counter(goal.goal))
    if goal.ctx:  # hypotheses count for less than the conclusion
        hyps = index.vec(sum((decl_counter(h) for h in goal.ctx), Counter()))
        g = {s: g.get(s, 0.0) + HYPS * hyps.get(s, 0.0) for s in g.keys() | hyps.keys()}
        norm = math.sqrt(sum(x * x for x in g.values())) or 1.0
        g = {s: x / norm for s, x in g.items()}
    last = max(len(index.entries) - 1, 1)
    scored = []
    for order, (name, pf) in enumerate(index.entries.values()):
        v = index[pf.thm]
        score = sum(x * v.get(s, 0.0) for s, x in g.items()) + 0.1 * order / last
        scored.append((score, name, pf))
    scored.sort(key=lambda t: -t[0])
    return scored


def report(
    goal: tactics.Goal | smt.BoolRef,
    k: int = 10,
    cutoff: float = 0.5,
    check: int = 3,
    timeout: int = 30,
    budget: float = 0.1,
) -> str:
    """
    The top `k` suggestions for `goal` as text, keeping only those scoring at least
    `cutoff` times the best. The top `check` are tried with z3.

    A suggestion marked ✅ proves the goal on its own. Checks stop once `budget`
    seconds have passed.
    """
    from kdrag.printers.pretty import pretty_expr

    thm = goal if isinstance(goal, smt.BoolRef) else goal.to_expr()
    ranked = rank(goal)[:k]
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
    if not lines:
        return ""
    return "Suggestions:\n" + "\n".join(lines)
