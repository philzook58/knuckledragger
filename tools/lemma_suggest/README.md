# Lemma suggestion benchmark

`kdrag.suggest` ranks library lemmas for a goal, and `l.suggest()` prints them mid-proof.
These scripts check the ranking against the lemmas that existing proofs actually pass in `by=`.

```
python tools/lemma_suggest/record.py calls.json   # import all theories, record every kd.prove call (~2.5s)
python tools/lemma_suggest/bench.py calls.json    # compare rankers on that data (<1s)
python tools/lemma_suggest/ltr.py calls.json      # scikit-learn learned rankers (needs scikit-learn)
```

Each call is scored only against lemmas that existed before it, so there's no leakage from
later lemmas. The recording covers 816 library lemmas (561 proved, 255 definitions) and 1068
`prove` calls; 438 of the calls use library lemmas.

## Results (2026-11-22)

hit@10 is the fraction of calls with a used lemma in the top 10. "Old lemmas" are used lemmas that
aren't among the 10 most recent, so recency alone can't find them.

| ranker | hit@10 all | hit@10 lemmas only | hit@10 old lemmas | MRR all |
|---|---|---|---|---|
| recency | 0.72 | 0.61 | 0.00 | 0.32 |
| symbol tf-idf cosine (MePo/SInE-like) | 0.92 | 0.83 | 0.70 | 0.46 |
| k-NN over earlier calls (MaSh-like) | 0.66 | 0.54 | 0.61 | 0.49 |
| mix (symbols + k-NN + recency) | 0.97 | 0.89 | 0.81 | 0.62 |
| logistic regression, held-out modules | 0.94 | | | 0.65 |
| gradient boosting, held-out modules | 0.87 | | | 0.62 |

- The learned models don't beat the hand-built mix with only about 440 training calls.
  scikit-learn isn't worth the dependency yet.
- A cutoff (show only lemmas scoring at least half the top score) shows about 5 instead of 10,
  with hit 0.90 instead of 0.97 and roughly double the precision.

Live check on 301 goals from the real, int, seq and zf theories, with only lemmas that existed
at each goal (`kdrag.suggest` as shipped: symbols plus recency, no k-NN, conclusion weighted over
hypotheses):

- A used lemma is among the suggestions shown for 93% of goals.
- z3 proves 10 goals with no lemma. For 179 of the other 291 (62%), one of the top-3 suggestions
  proves the goal on its own: those are the ✓ marks.
- Ranking takes about 1-2ms. Each z3 check takes about 2ms at the median, capped at 30ms. The
  first call indexes the library, which takes about 75ms.

k-NN is left out of `kdrag.suggest` for now. It needs a hook in `kd.prove` to record history,
and live it didn't help once the cutoff was applied (84% vs 92% shown).
