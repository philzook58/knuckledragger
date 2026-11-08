[real_analysis.py](real_analysis.py) builds continuous functions using addition and multiplication,
then derives pointwise continuity and limits using shared lemmas.
The theory proves pointwise closure first, then lifts it to global continuity.
General limit rules reuse pointwise continuity by updating the value at the limit point.
Run it with `uv run python examples/real_analysis.py`.

Run `uv run pytest tests/test_examples.py::test_real_analysis -s` for solver timings.
The test excludes imports and fails if a solver check or proof takes 0.5 seconds or longer.

Other ideas:

- <http://www.concrete-semantics.org/>
- <https://functional-algorithms-verified.org/>
- <https://math-comp.github.io/mcb/>
- <http://adam.chlipala.net/cpdt/>
- <http://adam.chlipala.net/frap/>
- Paulson Blog Posts
  - <https://lawrencecpaulson.github.io/2025/01/06/Code_Generation.html>
  - <https://lawrencecpaulson.github.io/2024/12/20/Quickstart.html>
