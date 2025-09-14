import kdrag.smt as smt
from dataclasses import dataclass
from collections import defaultdict
import itertools
import copy
import graphviz
# TODO: prune on models


@dataclass
class EGraph:
    roots: defaultdict[smt.SortRef, set[int]]
    terms: dict[int, smt.ExprRef]
    uf: dict[int, int]
    solver: smt.Solver
    reasons: dict[int, object]

    def __init__(self, proof=False):
        self.roots = defaultdict(set)
        self.terms = {}
        self.uf = {}
        self.reasons = {}
        self.proof = proof
        self.solver = smt.Solver()
        if proof:
            self.solver.set("unsat_core", True)

    def copy(self):
        """
        Copy the egraph. This is a shallow copy, so the terms are not copied.

        >>> E = EGraph()
        >>> f = smt.Function('f', smt.IntSort(), smt.IntSort())
        >>> x,y,z = smt.Ints('x y z')
        >>> E.add_term(f(x))
        >>> E.add_term(f(y))
        >>> _ = E.union(x,y)
        >>> assert E.find(f(x)) != E.find(f(y))
        >>> E2 = E.copy()
        >>> _ = E2.rebuild()
        >>> assert E2.find(f(x)) == E2.find(f(y))
        >>> assert E.find(f(x)) != E.find(f(y))
        """
        new = EGraph()
        new.roots = defaultdict(set, {k: v.copy() for k, v in self.roots.items()})
        new.terms = self.terms.copy()
        new.uf = self.uf.copy()
        self.reasons = self.reasons.copy()
        self.proof = self.proof
        new.solver = copy.copy(self.solver)
        return new

    def _find(self, eid: int) -> int:
        while eid in self.uf:  # invariant: root not in uf.
            eid = self.uf[eid]
        return eid

    def find(self, t: smt.ExprRef) -> int:
        """Get canonical id of term in egraph."""
        eid = t.get_id()
        return self._find(eid)

    def _union(self, t1: smt.ExprRef, t2: smt.ExprRef) -> bool:
        """Union only into union find."""
        root1, root2 = self.find(t1), self.find(t2)
        if root1 != root2:
            # strong union redundancy removal using SMT?
            self.uf[root1] = root2
            sort = t1.sort()
            self.roots[sort].discard(root1)
            return True
        else:
            return False

    def is_eq(self, t1: smt.ExprRef, t2: smt.ExprRef) -> bool:
        """
        Check if two terms are equal in the EGraph.

        >>> x,y,z = smt.Ints('x y z')
        >>> E = EGraph()
        >>> _ = E.union(x, y)
        >>> assert E.is_eq(x, y)
        >>> assert not E.is_eq(x, z)
        """
        eid1, eid2 = self.find(t1), self.find(t2)
        if eid1 == eid2:
            return True
        else:
            with self.solver:
                self.solver.add(t1 != t2)
                res = self.solver.check()
            return res == smt.unsat

    def union(self, t1: smt.ExprRef, t2: smt.ExprRef, add=True, reason=None) -> bool:
        """
        Assert equal two terms in the EGraph.
        Note that this does not add the terms to the EGraph.

        >>> x,y,z = smt.Ints('x y z')
        >>> E = EGraph()
        >>> _ = E.union(x, y)
        >>> assert E.find(x) == E.find(y)
        """
        if add:
            self.add_term(t1)
            self.add_term(t2)
        if self._union(t1, t2):
            if self.proof:
                p = smt.FreshConst(smt.BoolSort())
                self.reasons[p.get_id()] = (t1, t2, reason)
                self.solver.assert_and_track(t1 == t2, p)
            else:
                self.solver.add(t1 == t2)
            return True
        else:
            return False

    def add_term(self, t: smt.ExprRef) -> None:
        """
        Recursively add term to egraph
        """
        assert smt.is_app(t)
        eid = t.get_id()
        # TODO: Quantifier norm
        assert not isinstance(t, smt.QuantifierRef)
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
        with self.solver:
            self.solver.add(
                smt.And([t != self.terms[rid] for rid in self.roots[t.sort()]])
            )
            res = self.solver.check()
        return res == smt.unsat

    def rebuild(self) -> list[tuple[smt.ExprRef, smt.ExprRef]]:
        """
        >>> E = EGraph()
        >>> f = smt.Function('f', smt.IntSort(), smt.IntSort())
        >>> x,y,z = smt.Ints('x y z')
        >>> E.add_term(f(x))
        >>> E.add_term(f(y))
        >>> _ = E.union(x,y)
        >>> assert E.find(f(x)) != E.find(f(y))
        >>> E.rebuild()
        [(f(...), f(...))]
        >>> assert E.find(f(x)) == E.find(f(y))
        """
        propagates = []
        for sort, roots in self.roots.items():
            oldroots = list(roots)
            for n, eid1 in enumerate(oldroots):
                for eid2 in oldroots[:n]:
                    # Could do this better. The loop shrinks as we go along.
                    # could also prune with models
                    t1, t2 = self.terms[eid1], self.terms[eid2]
                    if self.find(t1) != self.find(t2):
                        with self.solver:
                            self.solver.add(t1 != t2)
                            res = self.solver.check()
                        if res == smt.unsat:
                            self._union(t1, t2)
                            propagates.append((t1, t2))
        return propagates

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

    def simplify_terms(self):
        """
        Use built in simplifier to simplify all terms in the egraph.
        Similar to "extract and simplify".

        >>> E = EGraph()
        >>> x,y,z = smt.Ints('x y z')
        >>> E.add_term(4 + x + y + 7)
        >>> E.add_term(8 + x + y + 3)
        >>> E.simplify_terms()
        >>> assert E.find(8 + x + y + 3) == E.find(4 + x + y + 7)
        """
        todo = []
        for t in self.terms.values():
            t1 = smt.simplify(t)
            if not t1.eq(t):
                todo.append((t, t1))
        for t, t1 in todo:
            self.add_term(t1)
            self._union(t, t1)

    def iter(self, vs: list[smt.ExprRef]):
        return [
            [self.terms[eid] for eid in eids]
            for eids in itertools.product(*[self.roots[v.sort()] for v in vs])
        ]

    def ematch(
        self, vs: list[smt.ExprRef], pat: smt.ExprRef
    ) -> list[list[smt.ExprRef]]:
        """
        Find all matches of pat in the egraph.

        >>> E = EGraph()
        >>> f = smt.Function('f', smt.IntSort(), smt.IntSort())
        >>> x,y,z = smt.Ints('x y z')
        >>> E.add_term(f(x))
        >>> _ = E.union(f(x), x)
        >>> _ = E.rebuild()
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

    def extract(self, t0: smt.ExprRef, cost_fun=(lambda _: 1)):
        """
        Extract a term from the egraph.

        >>> E = EGraph()
        >>> x,y,z = smt.Ints('x y z')
        >>> E.add_term(x + y)
        >>> _ = E.rebuild()
        >>> E.extract(x + y)
        x + y
        >>> _ = E.union(x + y, y)
        >>> _ = E.rebuild()
        >>> E.extract(x + y)
        y
        """
        inf = float("inf")
        best_cost = defaultdict(lambda: inf)
        best = {}
        while True:
            done = True
            # Terms are taking the place of enodes.
            for t in self.terms.values():
                eid = self.find(t)
                cost = cost_fun(t) + sum(
                    [best_cost[self.find(c)] for c in t.children()]
                )  # cost_fun(t.decl()) ?
                if cost < best_cost[eid]:
                    best_cost[eid] = cost
                    best[eid] = t
                    done = False
            if done:
                break

        # @functools.cache
        def build_best(t):
            t1 = best[self.find(t)]
            return t1.decl()(*[build_best(c) for c in t1.children()])

        return build_best(t0)

    def get_proof(self, t1: smt.ExprRef, t2: smt.ExprRef) -> list[object]:
        """
        Get the proof of why t1 == t2 in the egraph.
        The reasons returns may require recursive calls of get_proof.


        >>> E = EGraph(proof=True)
        >>> x,y,z = smt.Ints('x y z')
        >>> E.add_term(x + y)
        >>> _ = E.union(x + y, y, reason="because I said so")
        >>> _ = E.union(x + y, x, reason="because I said so too")
        >>> _ = E.union(x + y, z, reason="because I said so three")
        >>> list(sorted(E.get_proof(x, y), key=lambda x: x[2]))
        [(x + y, y, 'because I said so'), (x + y, x, 'because I said so too')]

        """
        with self.solver:
            self.solver.add(t1 != t2)
            res = self.solver.check()
            assert res == smt.unsat
            cores = self.solver.unsat_core()
        return [self.reasons[p.get_id()] for p in cores]

    def eclasses(
        self,
    ) -> defaultdict[int, defaultdict[smt.FuncDeclRef, set[tuple[int]]]]:
        """
        Returns a dictionary mapping each term to its equivalence class.

        >>> E = EGraph()
        >>> x,y,z = smt.Ints("x y z")
        >>> E.add_term(x + y)
        >>> E.union(y,z)
        True
        >>> _ = E.rebuild()
        >>> _ = E.eclasses()
        """
        eclasses = defaultdict(lambda: defaultdict(set))
        # building eclass table: eid,funcdecl -> arg_eids
        for t in self.terms.values():
            eid = self.find(t)
            f, args = t.decl(), tuple(self.find(a) for a in t.children())
            eclasses[eid][f].add(args)
        return eclasses

    def dot(self, filename: str = "egraph") -> graphviz.Digraph:
        """
        Create graphviz representation of the egraph.

        >>> E = EGraph()
        >>> x,y,z = smt.Ints("x y z")
        >>> E.add_term(x + y)
        >>> E.union(y,z)
        True
        >>> _ = E.rebuild()
        >>> _ = E.dot()
        """
        dot = graphviz.Digraph(filename, format="png")
        eclasses = self.eclasses()

        for eid, funcs in eclasses.items():
            with dot.subgraph(name=f"cluster_{eid}") as c:  # type: ignore
                assert c is not None
                c.attr(style="dotted,rounded")
                rep = f"e_rep_{eid}"
                c.node(rep, label="", shape="point", style="invis")
                # create one node per enode in this class
                for f, arg_sets in funcs.items():
                    for args in arg_sets:
                        name = f.name()
                        name = (
                            str(f()) if name == "Int" or name == "Real" else name
                        )  # fixup for some constants
                        node_id = f"{eid}_{name}_" + "_".join(map(str, args))
                        c.node(node_id, label=name, shape="box", style="rounded")
                        # connect each enode to its children’s rep‐points
                        for child_eid in args:
                            dot.edge(node_id, f"e_rep_{child_eid}")
        return dot
