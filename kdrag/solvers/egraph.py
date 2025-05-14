import kdrag.smt as smt
from dataclasses import dataclass
from collections import defaultdict
import itertools
import copy

# TODO: prune on models
# TODO: extract
# TODO: Proofs


@dataclass
class EGraph:
    roots: defaultdict[smt.SortRef, set[int]]
    terms: dict[int, smt.ExprRef]
    uf: dict[int, int]
    solver: smt.Solver

    def __init__(self):
        self.roots = defaultdict(set)
        self.terms = {}
        self.uf = {}
        self.solver = smt.Solver()

    def copy(self):
        """
        Copy the egraph. This is a shallow copy, so the terms are not copied.

        >>> E = EGraph()
        >>> f = smt.Function('f', smt.IntSort(), smt.IntSort())
        >>> x,y,z = smt.Ints('x y z')
        >>> E.add_term(f(x))
        >>> E.add_term(f(y))
        >>> E.union(x,y)
        >>> assert E.find(f(x)) != E.find(f(y))
        >>> E2 = E.copy()
        >>> E2.rebuild()
        >>> assert E2.find(f(x)) == E2.find(f(y))
        >>> assert E.find(f(x)) != E.find(f(y))
        """
        new = EGraph()
        new.roots = defaultdict(set, {k: v.copy() for k, v in self.roots.items()})
        new.terms = self.terms.copy()
        new.uf = self.uf.copy()
        new.solver = copy.copy(self.solver)
        return new

    def _find(self, eid: int) -> int:
        while eid in self.uf:  # invariant: root not in uf.
            eid = self.uf[eid]
        return eid

    def find(self, t: smt.ExprRef) -> int:
        eid = t.get_id()
        return self._find(eid)

    def union(self, t1: smt.ExprRef, t2: smt.ExprRef) -> None:
        """
        Assert equal two terms in the EGraph.
        Note that this does not add the terms to the EGraph.

        >>> x,y,z = smt.Ints('x y z')
        >>> E = EGraph()
        >>> E.union(x, y)
        >>> assert E.find(x) == E.find(y)
        """
        root1, root2 = self.find(t1), self.find(t2)
        if root1 != root2:
            self.uf[root1] = root2
            sort = t1.sort()
            self.roots[sort].discard(root1)
            self.solver.add(t1 == t2)

    def add_term(self, t: smt.ExprRef) -> None:
        """
        Recursively add term to egraph
        """
        eid = t.get_id()
        if eid not in self.terms:
            self.roots[t.sort()].add(eid)
            self.terms[eid] = t
            for arg in t.children():
                self.add_term(arg)

    def in_terms(self, t: smt.ExprRef) -> bool:
        """
        Semantically check if t is in termbank

        >>> x,y,z = smt.Ints('x y z')
        >>> E = EGraph()
        >>> E.add_term(x + y)
        >>> assert E.in_terms(x)
        >>> assert not E.in_terms(z)
        """
        if t.get_id() in self.terms:  # fast path
            return True
        # semantically distinct from all roots
        self.solver.push()
        self.solver.add(smt.And([t != self.terms[rid] for rid in self.roots[t.sort()]]))
        res = self.solver.check()
        self.solver.pop()
        return res == smt.unsat

    def rebuild(self):
        """
        >>> E = EGraph()
        >>> f = smt.Function('f', smt.IntSort(), smt.IntSort())
        >>> x,y,z = smt.Ints('x y z')
        >>> E.add_term(f(x))
        >>> E.add_term(f(y))
        >>> E.union(x,y)
        >>> assert E.find(f(x)) != E.find(f(y))
        >>> E.rebuild()
        >>> assert E.find(f(x)) == E.find(f(y))
        """

        for sort, roots in self.roots.items():
            oldroots = list(roots)
            for n, eid1 in enumerate(oldroots):
                for eid2 in oldroots[:n]:
                    # Could do this better. The loop shrinks as we go along.
                    # could also prune with models
                    t1, t2 = self.terms[eid1], self.terms[eid2]
                    if self.find(t1) != self.find(t2):
                        self.solver.push()
                        self.solver.add(t1 != t2)
                        res = self.solver.check()
                        self.solver.pop()
                        if res == smt.unsat:
                            self.union(t1, t2)  # don't need to solver.add but whatev

    def rw(self, sorts: list[smt.SortRef], f):
        """
        Bottom up ematch and rewrite.
        f should take one argumentsper each sort in sorts
        and return a tuple of two terms (lhs, rhs)

        >>> E = EGraph()
        >>> f = smt.Function('f', smt.IntSort(), smt.IntSort())
        >>> x,y,z = smt.Ints('x y z')
        >>> E.add_term(f(x))
        >>> E.rw([smt.IntSort()], lambda v: (f(v), v + 1))
        >>> assert E.find(f(x)) == E.find(x + 1)

        """
        for vs in itertools.product(*[self.roots[sort] for sort in sorts]):
            vs = [self.terms[v] for v in vs]
            (lhs, rhs) = f(*vs)
            if self.in_terms(lhs):
                self.add_term(rhs)
                self.union(lhs, rhs)

    def ematch(
        self, vs: list[smt.ExprRef], pat: smt.ExprRef
    ) -> list[list[smt.ExprRef]]:
        """
        Find all matches of pat in the egraph.

        >>> E = EGraph()
        >>> f = smt.Function('f', smt.IntSort(), smt.IntSort())
        >>> x,y,z = smt.Ints('x y z')
        >>> E.add_term(f(x))
        >>> E.union(f(x), x)
        >>> E.rebuild()
        >>> E.ematch([y], f(f(y)))
        [[x]]
        """
        res = []
        for eids in itertools.product(*[self.roots[v.sort()] for v in vs]):
            ts = [self.terms[eid] for eid in eids]
            lhs = smt.substitute(pat, *zip(vs, ts))
            if self.in_terms(lhs):
                res.append(ts)
        return res
