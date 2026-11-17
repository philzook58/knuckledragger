# SBV case-splitting prototype

[case_split.py](case_split.py) adapts Levent Erkok's
[SBV CaseSplit example](https://github.com/LeventErkok/sbv/blob/0e9b17044cbdbf0d2395a43d0de37aaddf9be84b/Documentation/SBV/Examples/TP/CaseSplit.hs).
The upstream copyright and BSD license are retained in [LICENSE](LICENSE).

The polynomial is written directly in the theorem statement. Its proof uses:

```python
pf.cases(n % 3 == 0, n % 3 == 1, n % 3 == 2, timeout=100)
```

With two or more Boolean conditions, `cases` first proves their disjunction
under the current context, then opens branches in argument order. Overlapping
conditions are allowed. Failed or timed-out coverage checks preserve the proof
state. The timeout is in milliseconds and applies to the coverage check.

One argument retains the existing behavior: Boolean true/false cases or
datatype constructor cases. This branch prototypes only that extension and
this example.

Run from the repository root with dependencies installed:

```sh
PYTHONPATH=src python examples/sbv/case_split.py
```
