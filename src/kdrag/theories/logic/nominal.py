import kdrag as kd
from kdrag import FreshVars, QImplies, prove
from kdrag.smt import Consts, DeclareSort, If, Implies

Atom = DeclareSort("Atom")
a, b, c, x = Consts("a b c x", Atom)
A, B, C, X = FreshVars("A B C X", Atom)

# fresh is a # x
fresh = kd.notation.SortDispatch("fresh")
fresh.define([x, a], a != x)

not_fresh_idem = prove(~fresh(A, A), unfold=1).forall([A])
disjoint_fresh = prove(Implies(A != X, fresh(X, A)), unfold=1).forall([A, X])

# swap is (a b) . x
swap = kd.notation.SortDispatch("swap")
swap.define([x, a, b], If(x == a, b, If(x == b, a, x)))


swap_id = prove(swap(X, A, A) == X, unfold=1).forall([X, A])

equivariant = prove(
    QImplies(fresh(X, A), fresh(X, B), swap(X, A, B) == X), unfold=1
).forall([X, A, B])


def test():
    """
    >>> True
    True
    """
