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


@dataclass(repr=False)  # the default repr would print the whole library
class Index:
    """Library lemmas and definitions found by `utils.lemma_db`, oldest first."""

    # All keyed by `thm.get_id()`, except `idf`.
    entries: dict[int, tuple[str, kernel.Proof]] = field(default_factory=dict)
    syms: dict[int, Counter[smt.FuncDeclRef]] = field(default_factory=dict)
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
                self.syms[key] = decl_counter(pf.thm)
        if len(self.entries) != n:
            df = Counter(s for syms in self.syms.values() for s in syms)
            self.idf = {s: math.log(len(self.entries) / c) for s, c in df.items()}
            self.vecs = {}

    def vec(
        self, syms: Counter[smt.FuncDeclRef], ops=0.1
    ) -> dict[smt.FuncDeclRef, float]:
        """tf-idf vector; built-in operators are down-weighted by `ops`."""
        default = math.log(len(self.entries) + 1)
        v = {}
        for s, n in syms.items():
            w = 1.0 if smt.is_uninterp(s) else ops
            v[s] = w * (1 + math.log(n)) * self.idf.get(s, default)
        norm = math.sqrt(sum(x * x for x in v.values())) or 1.0
        return {s: x / norm for s, x in v.items()}

    def __getitem__(self, thm: smt.ExprRef) -> dict[smt.FuncDeclRef, float]:
        """tf-idf vector of an indexed theorem, cached."""
        key = thm.get_id()
        if key not in self.vecs:
            self.vecs[key] = self.vec(self.syms[key])
        return self.vecs[key]


index = Index()


HYPS = 0.3  # weight of hypothesis symbols relative to the conclusion's


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
    top = scored[0][0]
    return [(name, pf) for score, name, pf in scored[:k] if score >= cutoff * top]


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

    thm = goal if isinstance(goal, smt.BoolRef) else goal.to_expr()
    start = time.perf_counter()
    lines = []
    for i, (name, pf) in enumerate(rank(goal)):
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
