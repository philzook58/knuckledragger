Knuckledragger
==============

Knuckledragger is an interactive proof assistant for Python built on Z3.
Use it to state and prove properties of programs, algebraic structures,
and real-valued functions.

.. toctree::
   :maxdepth: 1

   real
   theorems
   api

Getting started
---------------

Install with ``uv pip install git+https://github.com/philzook58/knuckledragger.git``.

Use ``prove`` for a single solver call and ``@Theorem`` when you want to guide
the proof in steps.

.. doctest::

   >>> from kdrag import Theorem, pretty_expr
   >>> from kdrag.smt import ForAll, Int
   >>> x = Int("x")
   >>> @Theorem(ForAll(x, x > 0, x + 1 > 0))
   ... def add_one_pos(l):
   ...     l.fix()
   ...     l.intros()
   ...     l.auto()
   >>> print(pretty_expr(add_one_pos.thm))
   ∀x : ℤ, x > 0 → x + 1 > 0

See the `introductory notebook <https://github.com/philzook58/knuckledragger/blob/main/tutorial.ipynb>`_
for definitions and induction. The `project README <https://github.com/philzook58/knuckledragger#readme>`_
collects the longer examples, design notes, and historical posts.
