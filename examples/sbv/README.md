# SBV theorem-proving examples

Adapted from [Levent Erkok’s SBV examples](https://github.com/LeventErkok/sbv/tree/0e9b17044cbdbf0d2395a43d0de37aaddf9be84b/Documentation/SBV/Examples/TP).
The upstream copyright and BSD license are retained in [LICENSE](LICENSE).

- [CaseSplit](case_split.py): prove `2*n*n + n + 1` is never divisible by 3.
  Splitting into the three possible remainders makes the solver’s job much easier.
- [RevAcc](rev_acc.py): prove accumulator reverse agrees with ordinary reverse.
  The key is the stronger invariant `rev_acc(acc, xs) = reverse(xs) ++ acc`:
  keep `acc` quantified during induction, then specialize it to the empty list.

These use finite SMT sequences, default empty/cons induction, and `[x] + xs`
notation. `pf.eq` handles the calculation using the existing proof context.
SBV’s list patterns and automatic termination checks remain useful features
for comparison; knuckledragger’s `define` does not check termination.

Run from the repository root with dependencies installed:

```sh
PYTHONPATH=src python examples/sbv/case_split.py
PYTHONPATH=src python examples/sbv/rev_acc.py
```
