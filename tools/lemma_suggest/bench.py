"""Rank library lemmas for recorded prove calls; score against the lemmas actually used.

    python tools/lemma_suggest/bench.py calls.json

For each call whose `by=` used library lemmas, every ranker orders the lemmas that
existed before the call. A ranker is good if those lemmas land near the top.
"""

import json
import math
import sys
import time
from collections import Counter, defaultdict

data = json.load(open(sys.argv[1] if len(sys.argv) > 1 else "lemma_calls.json"))
lemmas = data["lemmas"]
calls = sorted(data["calls"], key=lambda c: c["tick"])
by_name = {lem["name"]: lem for lem in lemmas}


def features(symbols: dict, ops=0.0) -> dict[str, float]:
    """Symbol bag; built-in operators (`op:`) and sorts get weight `ops`."""
    out = {}
    for s, n in symbols.items():
        w = ops if s.startswith(("op:", "sort:")) else 1.0
        if w:
            out[s] = w * (1 + math.log(n))
    return out


# Document frequency over all library lemmas (a small, harmless leak of counts).
df = Counter(s for lem in lemmas for s in lem["symbols"])
idf = {s: math.log(len(lemmas) / n) for s, n in df.items()}


def tfidf(symbols: dict, ops=0.0) -> dict[str, float]:
    v = {
        s: w * idf.get(s, math.log(len(lemmas)))
        for s, w in features(symbols, ops).items()
    }
    norm = math.sqrt(sum(x * x for x in v.values())) or 1.0
    return {s: x / norm for s, x in v.items()}


def cos(u: dict, v: dict) -> float:
    if len(u) > len(v):
        u, v = v, u
    return sum(x * v.get(s, 0.0) for s, x in u.items())


for lem in lemmas:
    lem["vec"] = tfidf(lem["symbols"])
for c in calls:
    c["vec"] = tfidf(c["symbols"])


# --- rankers: (call, pool, history) -> {lemma name: score} -------------------


def recency(call, pool, history):
    return {lem["name"]: lem["tick"] for lem in pool}


def symbol_cos(call, pool, history):
    return {lem["name"]: cos(call["vec"], lem["vec"]) for lem in pool}


def knn(call, pool, history, k=20):
    """MaSh-style: lemmas used by the k most similar earlier goals."""
    sims = sorted(
        ((cos(call["vec"], h["vec"]), h) for h in history), key=lambda t: -t[0]
    )
    score: dict[str, float] = defaultdict(float)
    for s, h in sims[:k]:
        for t in h["targets"]:
            score[t] += s
    return dict(score)


def mix(call, pool, history, w_knn=1.0, w_sym=1.0, w_rec=0.3):
    sym = symbol_cos(call, pool, history)
    nn = knn(call, pool, history)
    top_nn = max(nn.values(), default=1.0) or 1.0
    ticks = sorted(lem["tick"] for lem in pool)
    rank_of_tick = {t: i / max(len(ticks) - 1, 1) for i, t in enumerate(ticks)}
    return {
        lem["name"]: w_sym * sym[lem["name"]]
        + w_knn * nn.get(lem["name"], 0.0) / top_nn
        + w_rec * rank_of_tick[lem["tick"]]
        for lem in pool
    }


RANKERS = {"recency": recency, "symbol_cos": symbol_cos, "knn": knn, "mix": mix}


def all_targets(targets, pool):
    return targets


def lemma_targets(targets, pool):
    """Proved lemmas only, not definitions."""
    return {t for t in targets if by_name[t]["kind"] == "lemma"}


def old_targets(targets, pool):
    """Proved lemmas that are not among the 10 most recent: recency can't find them."""
    recent = {lem["name"] for lem in sorted(pool, key=lambda lem: -lem["tick"])[:10]}
    return lemma_targets(targets, pool) - recent


SLICES = {"all": all_targets, "lemmas": lemma_targets, "old lemmas": old_targets}


def evaluate(ranker, ks=(1, 5, 10), keep=all_targets):
    hit = Counter()
    recall = Counter()
    mrr = 0.0
    n = 0
    worst = 0.0
    history = []
    for call in calls:
        pool = [lem for lem in lemmas if lem["tick"] < call["tick"]]
        targets = keep(set(call["targets"]) & {lem["name"] for lem in pool}, pool)
        if targets:
            t0 = time.perf_counter()
            scores = ranker(call, pool, history)
            ranked = sorted(pool, key=lambda lem: -scores.get(lem["name"], -1e9))
            worst = max(worst, time.perf_counter() - t0)
            names = [lem["name"] for lem in ranked]
            pos = {name: i for i, name in enumerate(names)}
            first = min(pos[t] for t in targets)
            mrr += 1 / (first + 1)
            for k in ks:
                hit[k] += first < k
                recall[k] += sum(pos[t] < k for t in targets) / len(targets)
            n += 1
        if call["targets"]:
            history.append(call)
    return (
        n,
        {k: hit[k] / n for k in ks},
        {k: recall[k] / n for k in ks},
        mrr / n,
        worst,
    )


if __name__ == "__main__":
    print(
        f"{len(lemmas)} lemmas, {sum(1 for c in calls if c['targets'])} calls with targets"
    )
    for slice_name, keep in SLICES.items():
        print(f"\n== targets: {slice_name}")
        print(
            f"{'ranker':12} {'n':>4} {'hit@1':>6} {'hit@5':>6} {'hit@10':>6} {'rec@10':>7} {'MRR':>6} {'worst ms':>9}"
        )
        for name, ranker in RANKERS.items():
            n, hit, rec, mrr, worst = evaluate(ranker, keep=keep)
            print(
                f"{name:12} {n:4} {hit[1]:6.2f} {hit[5]:6.2f} {hit[10]:6.2f} {rec[10]:7.2f} {mrr:6.2f} {worst * 1000:9.1f}"
            )
