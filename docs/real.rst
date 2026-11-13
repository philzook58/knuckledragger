Real analysis
=============

Start with ``kdrag.theories.real`` for real expressions, absolute value,
and the definitions of continuity and limits. A real function is an SMT
array from reals to reals. Use ``Lambda(x, body)`` to build one and ``f[x]``
to evaluate it.

* :ref:`real-continuity` covers continuity at a point, continuity everywhere,
  and pointwise limits. Start with ``continuous_at_sq`` for a concrete
  function and ``has_lim_at_of_cont_at`` for the connection between continuity
  and limits.
* :ref:`real-sequences` covers limits as the integer index tends to
  infinity. Start with ``has_lim_inv`` for convergence of ``1/n`` and
  ``lim_unique`` for uniqueness.
* :ref:`real-topology` covers distance, open balls, and open subsets of the reals.

.. _real-continuity:

Continuity and pointwise limits
-------------------------------

Use ``cont_at(f, p)`` to state continuity at ``p``, ``is_cont(f)`` for
continuity everywhere, and ``has_lim_at(f, p, y)`` for a limit with value
``y``. The last predicate uses a punctured neighborhood of ``p``.

.. doctest::

   >>> from kdrag import pretty_expr
   >>> from kdrag.theories.real.cont import has_lim_at_of_cont_at
   >>> print(pretty_expr(has_lim_at_of_cont_at.thm))
   ∀f : ℝ → ℝ, x : ℝ, cont_at(f, x) → has_lim_at(f, x, f[x])

Browse the statements in :ref:`cont-statements` or
`read the proofs <https://github.com/philzook58/knuckledragger/blob/main/src/kdrag/theories/real/cont.py>`_.

.. _real-sequences:

Sequence limits
---------------

Use ``has_lim(a, y)`` for the statement that a sequence converges to ``y``.
The definition asks for a nonnegative cutoff for each positive error
tolerance. Browse :ref:`seq-statements` for convergence, finite sums,
and other sequence lemmas. For closure under addition, multiplication, and
division, see the `sequence limit algebra source <https://github.com/philzook58/knuckledragger/blob/main/src/kdrag/theories/real/lim_algebra.py>`_.

.. _real-topology:

Distance and open sets
----------------------

The ``analysis`` module defines distance and openness using real absolute
value and open balls. See :ref:`analysis-statements` for the triangle
inequality and basic results about open sets.
