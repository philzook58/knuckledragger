"""First-order algebra through E, Vampire, and cvc5.

Run with ``python examples/portable_algebra.py``. Requires the packaged E prover,
Vampire, and the cvc5 executable. Associativity is an explicit hypothesis of the
theorem; this example adds no axioms to the library.
"""

from kdrag import prove
from kdrag.smt import Consts, DeclareSort, ForAll, Function
from kdrag.solvers import CVC5Solver, EProverSolver, VampireSolver


S = DeclareSort("PortableSemigroup")
mul = Function("semigroup_mul", S, S, S)
a, b, c, d = Consts("a b c d", S)

associative = ForAll([a, b, c], mul(mul(a, b), c) == mul(a, mul(b, c)))
reassociate_four = ForAll(
    [a, b, c, d],
    mul(mul(mul(a, b), c), d) == mul(a, mul(b, mul(c, d))),
)


def reassociate(solver):
    return prove(reassociate_four, assumes=[associative], solver=solver)


if __name__ == "__main__":
    for solver in (EProverSolver, VampireSolver, CVC5Solver):
        reassociate(solver)
        print(f"{solver.__name__}: proved four-factor reassociation")
