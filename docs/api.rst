Python API
==========

.. autofunction:: kdrag.smt.ForAll
.. autofunction:: kdrag.smt.Exists
.. autofunction:: kdrag.define

Proving formulas
----------------

.. autofunction:: kdrag.prove
.. autofunction:: kdrag.Theorem
.. autofunction:: kdrag.exact
.. autoclass:: kdrag.Calc
   :no-members:

Working on a proof
------------------

.. autofunction:: kdrag.PTheorem
.. autoclass:: kdrag.tactics.ProofState
   :members: fix, fixes, intros, auto, have, exact, specialize, rewrite, unfold
   :no-undoc-members:
   :no-inherited-members:

.. autofunction:: kdrag.pretty_expr
.. autofunction:: kdrag.printers.pretty.pretty_goal
