# SBV theorem-proving examples

Adapted from [Levent Erkok’s SBV examples](https://github.com/LeventErkok/sbv/tree/0e9b17044cbdbf0d2395a43d0de37aaddf9be84b/Documentation/SBV/Examples/TP).
The upstream copyright and BSD license are retained in [LICENSE](LICENSE).

- [CaseSplit](case_split.py): prove `2*n*n + n + 1` is never divisible by 3.
  Splitting into the three possible remainders makes the solver’s job much easier.
- [Coins](coins.py): make every amount at least 8 with 3- and 5-unit coins.
  Three consecutive base amounts support strong induction with a step of 3.
- [RevAcc](rev_acc.py): prove accumulator reverse agrees with ordinary reverse.
  The key is the stronger invariant `rev_acc(acc, xs) = reverse(xs) ++ acc`:
  keep `acc` quantified during induction, then specialize it to the empty list.
- [Fibonacci](fibonacci.py): prove tail-recursive and textbook Fibonacci agree.
  Describe the accumulators as consecutive Fibonacci numbers, keeping their
  starting index quantified so the induction hypothesis can shift it.
- [PigeonHole](pigeon_hole.py): if an integer list sums to more than its length,
  some entry exceeds 1. Compare native left folds with cons induction (requiring
  an accumulator lemma) and snoc induction (using the append equations directly).
  The snoc principle is derived from cons induction.
- [Tree](tree.py): mirroring is involutive, preserves size, and reverses traversal.
  Structural induction supplies both subtree hypotheses directly; SBV instead
  uses strong induction on tree size.

RevAcc uses finite SMT sequences, default empty/cons induction, and `[x] + xs`
notation. Fibonacci uses integer induction. `pf.eq` handles both calculations
using the existing proof context.
SBV’s list patterns and automatic termination checks remain useful features
for comparison; knuckledragger’s `define` does not check termination.

Run from the repository root with dependencies installed:

```sh
PYTHONPATH=src python examples/sbv/case_split.py
PYTHONPATH=src python examples/sbv/coins.py
PYTHONPATH=src python examples/sbv/rev_acc.py
PYTHONPATH=src python examples/sbv/fibonacci.py
PYTHONPATH=src python examples/sbv/pigeon_hole.py
PYTHONPATH=src python examples/sbv/tree.py
```
