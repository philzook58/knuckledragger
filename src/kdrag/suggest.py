"""
Suggest library lemmas that are likely to help prove a goal.

Lemmas are ranked by shared rare symbols (tf-idf cosine, as in Sledgehammer's MePo
and SInE filters) with a small bonus for recent lemmas, then the best few are tried
with z3. See `tools/lemma_suggest/` for the benchmark against existing proofs.
"""

import math
import sys
import time
from collections import Counter
from typing import NamedTuple

import kdrag.kernel as kernel
import kdrag.smt as smt


def symbols(e: smt.ExprRef) -> Counter:
    """Function symbols in `e`: uninterpreted names, plus `op:`/`sort:` for built-ins."""
    out: Counter = Counter()
    seen = set()
    todo = [e]
    while todo:
        t = todo.pop()
        if t.get_id() in seen:
            continue
        seen.add(t.get_id())
        if isinstance(t, smt.QuantifierRef):
            for i in range(t.num_vars()):
                out["sort:" + str(t.var_sort(i))] += 1
            todo.append(t.body())
        elif smt.is_app(t):
            d = t.decl()
            if smt.is_uninterp(d):
                if "!" not in d.name():  # skip fresh variables like x!7
                    out[d.name()] += 1
            else:
                out["op:" + d.name()] += 1
            todo.extend(t.children())
    return out


def decl_names() -> dict[int, str]:
    """
    Python variable names bound to function symbols, keyed by `get_id()`.

    Definitions are shown as `fmul.defn`, as written, rather than z3's internal
    name (`(Array Real Real).mul`). The user's script is preferred.
    """
    out: dict[int, str] = {}
    for _, mod in sorted(sys.modules.items(), key=lambda kv: kv[0] != "__main__"):
        for k, v in list(getattr(mod, "__dict__", {}).items()):
            if isinstance(v, smt.FuncDeclRef) and not k.startswith("_"):
                out.setdefault(v.get_id(), k)
    return out


class Entry(NamedTuple):
    name: str
    proof: kernel.Proof
    symbols: Counter
    order: int  # discovery order, a proxy for recency


class Suggestion(NamedTuple):
    name: str
    proof: kernel.Proof
    score: float


class Index:
    """Library lemmas: module-level `Proof`s and definitional axioms."""

    def __init__(self):
        self.entries: dict[int, Entry] = {}
        self._modules: dict[str, int] = {}  # module name -> len(vars) when scanned
        self._ndefns = 0
        self._idf: dict[str, float] = {}
        self._vecs: dict[int, dict[str, float]] = {}

    def _add(self, name: str, pf: kernel.Proof):
        key = pf.thm.get_id()
        if key not in self.entries:
            self.entries[key] = Entry(name, pf, symbols(pf.thm), len(self.entries))

    def refresh(self):
        n = len(self.entries)
        mods = sorted(sys.modules.items(), key=lambda kv: kv[0] == "__main__")
        for mname, mod in mods:
            d = getattr(mod, "__dict__", None)
            if d is None or self._modules.get(mname) == len(d):
                continue
            self._modules[mname] = len(d)
            for k, v in list(d.items()):
                if isinstance(v, kernel.Proof) and not k.startswith("_"):
                    self._add(f"{mname}.{k}", v)
        if len(kernel.defns) != self._ndefns:
            self._ndefns = len(kernel.defns)
            names = decl_names()
            for decl, unfold in list(kernel.defns.items()):
                name = names.get(decl.get_id(), decl.name())
                self._add(f"{name}.defn", unfold.ax)
        if len(self.entries) != n:
            df = Counter(s for e in self.entries.values() for s in e.symbols)
            self._idf = {s: math.log(len(self.entries) / c) for s, c in df.items()}
            self._vecs = {}

    def vec(self, syms: Counter, ops=0.1) -> dict[str, float]:
        """tf-idf vector; built-in operators and sorts are down-weighted by `ops`."""
        default = math.log(len(self.entries) + 1)
        v = {}
        for s, n in syms.items():
            w = ops if s.startswith(("op:", "sort:")) else 1.0
            if w:
                v[s] = w * (1 + math.log(n)) * self._idf.get(s, default)
        norm = math.sqrt(sum(x * x for x in v.values())) or 1.0
        return {s: x / norm for s, x in v.items()}

    def entry_vec(self, key: int) -> dict[str, float]:
        v = self._vecs.get(key)
        if v is None:
            v = self._vecs[key] = self.vec(self.entries[key].symbols)
        return v


index = Index()


def _cos(u: dict, v: dict) -> float:
    if len(u) > len(v):
        u, v = v, u
    return sum(x * v.get(s, 0.0) for s, x in u.items())


HYPS = 0.3  # weight of hypothesis symbols relative to the conclusion's


def goal_vec(goal: smt.BoolRef) -> dict[str, float]:
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


def rank(goal: smt.BoolRef, k: int = 10, cutoff: float = 0.5) -> list[Suggestion]:
    """
    Library lemmas most likely to help prove `goal`, best first.

    The score is the tf-idf cosine of shared symbols plus a small recency bonus. At
    most `k` are returned, and only those scoring at least `cutoff` times the best.
    """
    index.refresh()
    if not index.entries:
        return []
    g = goal_vec(goal)
    last = max(len(index.entries) - 1, 1)
    score = {
        key: _cos(g, index.entry_vec(key)) + 0.1 * e.order / last
        for key, e in index.entries.items()
    }
    best = sorted(score, key=lambda key: -score[key])[:k]
    top = score[best[0]]
    return [
        Suggestion(index.entries[key].name, index.entries[key].proof, score[key])
        for key in best
        if score[key] >= cutoff * top
    ]


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
    for i, s in enumerate(rank(goal)):
        mark = "- "  # two columns, like the emoji
        if i < check and time.perf_counter() - start < budget:
            try:
                kernel.prove(goal, by=[s.proof], timeout=timeout)
                mark = "✅"
            except Exception:
                pass
        stmt = " ".join(pretty_expr(s.proof.thm).split())
        if len(stmt) > 70:
            stmt = stmt[:67] + "..."
        lines.append(f"  {mark} {s.name.removeprefix('kdrag.theories.')}: {stmt}")
    if not lines:
        return ""
    return "Suggestions:\n" + "\n".join(lines)
