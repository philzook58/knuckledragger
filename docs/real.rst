Real analysis
=============

* `real.cont <theorems.html#kdrag-theories-real-cont>`_
* `real.seq <theorems.html#kdrag-theories-real-seq>`_
* `real.analysis <theorems.html#kdrag-theories-real-analysis>`_
* `Sequence limit algebra source <https://github.com/philzook58/knuckledragger/blob/main/src/kdrag/theories/real/lim_algebra.py>`_

Continuity and pointwise limits
-------------------------------

.. doctest::

   >>> from kdrag import pretty_expr
   >>> from kdrag.theories.real.cont import has_lim_at_of_cont_at
   >>> print(pretty_expr(has_lim_at_of_cont_at.thm))
   ∀f : ℝ → ℝ, x : ℝ, cont_at(f, x) → has_lim_at(f, x, f[x])
