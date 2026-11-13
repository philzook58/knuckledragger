Knuckledragger
==============

.. toctree::
   :maxdepth: 1

   real
   theorems
   api

Getting started
---------------

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

* `Introductory notebook <https://github.com/philzook58/knuckledragger/blob/main/tutorial.ipynb>`_
* `Project README <https://github.com/philzook58/knuckledragger#readme>`_
