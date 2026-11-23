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
import kdrag.utils as utils


Symbol = smt.FuncDeclRef | smt.SortRef


def symbols(e: smt.ExprRef) -> Counter[Symbol]:
    """Function symbols in `e`, plus the sorts of its bound variables."""
    out: Counter[Symbol] = Counter()
    for t in utils.subterms(e, into_binder=True):
        if isinstance(t, smt.QuantifierRef):
            out.update(t.var_sort(i) for i in range(t.num_vars()))
        elif smt.is_app(t) and "!" not in t.decl().name():  # skip fresh x!7
            out[t.decl()] += 1
    return out


class Index:
    """Library lemmas and definitions found by `utils.lemma_db`, oldest first."""

    def __init__(self):
        self.entries: dict[int, tuple[str, kernel.Proof]] = {}  # by `thm.get_id()`
        self._syms: dict[int, Counter[Symbol]] = {}
        self._idf: dict[Symbol, float] = {}
        self._vecs: dict[int, dict[Symbol, float]] = {}

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

    def vec(self, syms: Counter[Symbol], ops=0.1) -> dict[Symbol, float]:
        """tf-idf vector; built-in operators and sorts are down-weighted by `ops`."""
        default = math.log(len(self.entries) + 1)
        v = {}
        for s, n in syms.items():
            w = 1.0 if isinstance(s, smt.FuncDeclRef) and smt.is_uninterp(s) else ops
            v[s] = w * (1 + math.log(n)) * self._idf.get(s, default)
        norm = math.sqrt(sum(x * x for x in v.values())) or 1.0
        return {s: x / norm for s, x in v.items()}

    def entry_vec(self, key: int) -> dict[Symbol, float]:
        v = self._vecs.get(key)
        if v is None:
            v = self._vecs[key] = self.vec(self._syms[key])
        return v


index = Index()


HYPS = 0.3  # weight of hypothesis symbols relative to the conclusion's


def goal_vec(goal: smt.BoolRef) -> dict[Symbol, float]:
    """Vector of `goal`, with hypotheses of a leading implication chain down-weighted."""
    hyps = []
    while smt.is_implies(goal):
        hyps.append(goal.arg(0))
        goal = goal.arg(1)
    v = dict(index.vec(symbols(goal)))
    if hyps:
        for s, x in index.vec(sum((symbols(h) for h in hyps), Counter())).items():
            v[s] = v.get(s, 0.0) + HYPS * x
        norm = math.sqrt(sum(x * x for x in v.values())) or 1.0
        v = {s: x / norm for s, x in v.items()}
    return v


def rank(
    goal: smt.BoolRef, k: int = 10, cutoff: float = 0.5
) -> list[tuple[str, kernel.Proof]]:
    """
    Names and proofs of the library lemmas most likely to help prove `goal`, best first.

    The score is the tf-idf cosine of shared symbols plus a small recency bonus. At
    most `k` are returned, and only those scoring at least `cutoff` times the best.
    """
    index.refresh()
    if not index.entries:
        return []
    g = goal_vec(goal)
    last = max(len(index.entries) - 1, 1)
    score = {}
    for order, key in enumerate(index.entries):
        v = index.entry_vec(key)
        score[key] = sum(x * v.get(s, 0.0) for s, x in g.items()) + 0.1 * order / last
    best = sorted(score, key=lambda key: -score[key])[:k]
    return [index.entries[key] for key in best if score[key] >= cutoff * score[best[0]]]


def report(
    goal: smt.BoolRef, check: int = 3, timeout: int = 30, budget: float = 0.1
) -> str:
    """
    Ranked suggestions for `goal` as text; the top `check` are tried with z3.

    A suggestion marked ✅ proves the goal on its own. Checks stop once `budget`
    seconds have passed.
    """
    from kdrag.printers.pretty import pretty_expr

    start = time.perf_counter()
    lines = []
    for i, (name, pf) in enumerate(rank(goal)):
        mark = "- "  # two columns, like the emoji
        if i < check and time.perf_counter() - start < budget:
            try:
                kernel.prove(goal, by=[pf], timeout=timeout)
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
