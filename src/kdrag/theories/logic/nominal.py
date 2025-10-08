import kdrag as kd
import kdrag.smt as smt

Atom = smt.DeclareSort("Atom")
a, b, c, x = smt.Consts("a b c x", Atom)
A, B, C, X = kd.FreshVars("A B C X", Atom)

# fresh is a # x
fresh = kd.notation.SortDispatch("fresh")
fresh.define([x, a], a != x)

not_fresh_idem = kd.prove(~fresh(A, A), unfold=1).forall([A])
disjoint_fresh = kd.prove(smt.Implies(A != X, fresh(X, A)), unfold=1).forall([A, X])

# swap is (a b) . x
swap = kd.notation.SortDispatch("swap")
swap.define([x, a, b], smt.If(x == a, b, smt.If(x == b, a, x)))


swap_id = kd.prove(swap(X, A, A) == X, unfold=1).forall([X, A])

equivariant = kd.prove(
    kd.QImplies(fresh(X, A), fresh(X, B), swap(X, A, B) == X), unfold=1
).forall([X, A, B])


def test():
    """
    >>> True
    True
    """
