"""Learning-to-rank experiment with scikit-learn, against the hand-built `mix` ranker.

    python tools/lemma_suggest/ltr.py calls.json

Each (call, candidate lemma) pair gets a few features; logistic regression learns
which pairs were used. Folds hold out whole theory modules, so the model is
always scored on proofs from modules it never trained on.
"""

import math
import sys
from collections import Counter

import numpy as np
from sklearn.linear_model import LogisticRegression
from sklearn.ensemble import HistGradientBoostingClassifier
from sklearn.model_selection import GroupKFold

sys.path.insert(0, "tools/lemma_suggest")
import bench  # noqa: E402

for lem in bench.lemmas:
    lem["vec_ops"] = bench.tfidf(lem["symbols"], 0.1)
    lem["module"] = lem["name"].rsplit(".", 1)[0] if lem["kind"] == "lemma" else ""
    lem["names"] = {s for s in lem["symbols"] if not s.startswith(("op:", "sort:"))}
for c in bench.calls:
    c["vec_ops"] = bench.tfidf(c["symbols"], 0.1)
    c["names"] = {s for s in c["symbols"] if not s.startswith(("op:", "sort:"))}

FEATURES = [
    "sym_cos",
    "sym_cos_ops",
    "knn",
    "recency",
    "is_defn",
    "same_module",
    "coverage",
    "max_shared_idf",
    "log_size",
    "popularity",
]

rows, labels, groups, query = [], [], [], []
history: list = []
used = Counter()
for qi, call in enumerate(bench.calls):
    pool = [lem for lem in bench.lemmas if lem["tick"] < call["tick"]]
    targets = set(call["targets"]) & {lem["name"] for lem in pool}
    if targets:
        nn = bench.knn(call, pool, history)
        top_nn = max(nn.values(), default=1.0) or 1.0
        ticks = sorted(lem["tick"] for lem in pool)
        rank = {t: i / max(len(ticks) - 1, 1) for i, t in enumerate(ticks)}
        for lem in pool:
            shared = call["names"] & lem["names"]
            rows.append(
                [
                    bench.cos(call["vec"], lem["vec"]),
                    bench.cos(call["vec_ops"], lem["vec_ops"]),
                    nn.get(lem["name"], 0.0) / top_nn,
                    rank[lem["tick"]],
                    lem["kind"] == "defn",
                    lem["module"] == call["module"],
                    len(shared) / max(len(lem["names"]), 1),
                    max((bench.idf.get(s, 0.0) for s in shared), default=0.0),
                    math.log(1 + sum(lem["symbols"].values())),
                    math.log(1 + used[lem["name"]]),
                ]
            )
            labels.append(lem["name"] in targets)
            groups.append(call["module"])
            query.append(qi)
    if call["targets"]:
        history.append(call)
        used.update(call["targets"])

X, y, groups, query = (
    np.array(rows, float),
    np.array(labels),
    np.array(groups),
    np.array(query),
)
print(f"{len(set(query))} queries, {len(y)} pairs, {y.sum()} positives")


def scores_to_metrics(score):
    hit10 = []
    mrr = []
    for q in np.unique(query):
        m = query == q
        order = np.argsort(-score[m])
        lab = y[m][order]
        first = np.argmax(lab)
        hit10.append(first < 10)
        mrr.append(1 / (first + 1))
    return np.mean(hit10), np.mean(mrr)


mix_score = (
    X[:, FEATURES.index("sym_cos_ops")]
    + X[:, FEATURES.index("knn")]
    + 0.1 * X[:, FEATURES.index("recency")]
)
print(f"{'model':22} hit@10   MRR")
print(
    f"{'mix (hand-built)':22} {scores_to_metrics(mix_score)[0]:.2f}   {scores_to_metrics(mix_score)[1]:.2f}"
)

for name, make in {
    "logistic regression": lambda: LogisticRegression(
        max_iter=2000, class_weight="balanced"
    ),
    "gradient boosting": lambda: HistGradientBoostingClassifier(max_iter=200),
}.items():
    pred = np.zeros(len(y))
    for train, test in GroupKFold(n_splits=5).split(X, y, groups):
        model = make().fit(X[train], y[train])
        pred[test] = model.predict_proba(X[test])[:, 1]
    hit, mrr = scores_to_metrics(pred)
    print(f"{name:22} {hit:.2f}   {mrr:.2f}")
    if name == "logistic regression":
        coef = make().fit(X, y).coef_[0]
        print("  weights:", ", ".join(f"{f}={c:+.1f}" for f, c in zip(FEATURES, coef)))
