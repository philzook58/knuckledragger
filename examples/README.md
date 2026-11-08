Continuity and limit lemmas live in
[real/cont.py](../src/kdrag/theories/real/cont.py).
Run `uv run pytest tests/test_real_cont.py::test_continuity -s` for solver timings.
The test excludes base-theory imports and fails if a solver check or proof takes
0.5 seconds or longer.

Other ideas:

- <http://www.concrete-semantics.org/>
- <https://functional-algorithms-verified.org/>
- <https://math-comp.github.io/mcb/>
- <http://adam.chlipala.net/cpdt/>
- <http://adam.chlipala.net/frap/>
- Paulson Blog Posts
  - <https://lawrencecpaulson.github.io/2025/01/06/Code_Generation.html>
  - <https://lawrencecpaulson.github.io/2024/12/20/Quickstart.html>
