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

import kdrag.kernel as kernel
import kdrag.smt as smt
import kdrag.tactics as tactics
import kdrag.utils as utils


def symbols(e: smt.ExprRef) -> Counter[smt.FuncDeclRef]:
    """Function symbols in `e`, skipping fresh variables like x!7."""
    return Counter(
        t.decl()
        for t in utils.subterms(e, into_binder=True)
        if smt.is_app(t) and "!" not in t.decl().name()
    )


class Index:
    """Library lemmas and definitions found by `utils.lemma_db`, oldest first."""

    def __init__(self):
        self.entries: dict[int, tuple[str, kernel.Proof]] = {}  # by `thm.get_id()`
        self._syms: dict[int, Counter[smt.FuncDeclRef]] = {}
        self._idf: dict[smt.FuncDeclRef, float] = {}
        self._vecs: dict[int, dict[smt.FuncDeclRef, float]] = {}

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
                self._syms[key] = symbols(pf.thm)
        if len(self.entries) != n:
            df = Counter(s for syms in self._syms.values() for s in syms)
            self._idf = {s: math.log(len(self.entries) / c) for s, c in df.items()}
            self._vecs = {}

    def vec(
        self, syms: Counter[smt.FuncDeclRef], ops=0.1
    ) -> dict[smt.FuncDeclRef, float]:
        """tf-idf vector; built-in operators are down-weighted by `ops`."""
        default = math.log(len(self.entries) + 1)
        v = {}
        for s, n in syms.items():
            w = 1.0 if smt.is_uninterp(s) else ops
            v[s] = w * (1 + math.log(n)) * self._idf.get(s, default)
        norm = math.sqrt(sum(x * x for x in v.values())) or 1.0
        return {s: x / norm for s, x in v.items()}

    def entry_vec(self, key: int) -> dict[smt.FuncDeclRef, float]:
        v = self._vecs.get(key)
        if v is None:
            v = self._vecs[key] = self.vec(self._syms[key])
        return v


index = Index()


HYPS = 0.3  # weight of hypothesis symbols relative to the conclusion's


def goal_vec(goal: tactics.Goal) -> dict[smt.FuncDeclRef, float]:
    """Vector of `goal`, with its hypotheses down-weighted."""
    v = index.vec(symbols(goal.goal))
    if goal.ctx:
        hyps = index.vec(sum((symbols(h) for h in goal.ctx), Counter()))
        v = {s: v.get(s, 0.0) + HYPS * hyps.get(s, 0.0) for s in v.keys() | hyps.keys()}
        norm = math.sqrt(sum(x * x for x in v.values())) or 1.0
        v = {s: x / norm for s, x in v.items()}
    return v


def _goal(goal: tactics.Goal | smt.BoolRef) -> tactics.Goal:
    if isinstance(goal, smt.BoolRef):
        return tactics.Goal(sig=[], ctx=[], goal=goal)
    return goal


def rank(
    goal: tactics.Goal | smt.BoolRef, k: int = 10, cutoff: float = 0.5
) -> list[tuple[str, kernel.Proof]]:
    """
    Names and proofs of the library lemmas most likely to help prove `goal`, best first.

    The score is the tf-idf cosine of shared symbols plus a small recency bonus. At
    most `k` are returned, and only those scoring at least `cutoff` times the best.
    """
    index.refresh()
    if not index.entries:
        return []
    g = goal_vec(_goal(goal))
    last = max(len(index.entries) - 1, 1)
    score = {}
    for order, key in enumerate(index.entries):
        v = index.entry_vec(key)
        score[key] = sum(x * v.get(s, 0.0) for s, x in g.items()) + 0.1 * order / last
    best = sorted(score, key=lambda key: -score[key])[:k]
    return [index.entries[key] for key in best if score[key] >= cutoff * score[best[0]]]


def report(
    goal: tactics.Goal | smt.BoolRef,
    check: int = 3,
    timeout: int = 30,
    budget: float = 0.1,
) -> str:
    """
    Ranked suggestions for `goal` as text; the top `check` are tried with z3.

    A suggestion marked ✅ proves the goal on its own. Checks stop once `budget`
    seconds have passed.
    """
    from kdrag.printers.pretty import pretty_expr

    goal = _goal(goal)
    start = time.perf_counter()
    lines = []
    for i, (name, pf) in enumerate(rank(goal)):
        mark = "- "  # two columns, like the emoji
        if i < check and time.perf_counter() - start < budget:
            try:
                kernel.prove(goal.to_expr(), by=[pf], timeout=timeout)
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
