from dataclasses import dataclass, field
from typing import Optional, NamedTuple
import kdrag.smt as smt


class GroundClause(NamedTuple):
    pos: tuple[smt.BoolRef]
    neg: tuple[smt.BoolRef]

    @classmethod
    def of_expr(cls, e: smt.BoolRef) -> "GroundClause":
        """

        >>> e = smt.Or(smt.Bool("a"), smt.Not(smt.Bool("b")), smt.Bool("c"))
        >>> GroundClause.of_expr(e)
        GroundClause(pos=(a, c), neg=(b,))
        """
        pos = []
        neg = []

        def collect(e: smt.BoolRef):
            if smt.is_or(e):
                for c in e.children():
                    collect(c)
            elif smt.is_not(e):
                neg.append(e.children()[0])
            else:
                pos.append(e)

        collect(e)
        return GroundClause(tuple(pos), tuple(neg))

    def to_expr(self) -> smt.BoolRef:
        """
        >>> c = GroundClause((smt.Bool("a"), smt.Bool("c")), (smt.Bool("b"),))
        >>> c.to_expr()
        Or(a, c, Not(b))
        """
        return smt.Or(*self.pos, *[smt.Not(n) for n in self.neg])


type Var = int  # Var should always be positive
type Lit = int  # Lits can be negative to indicate logical negation
type Clause = list[Lit]


@dataclass
class DPLLSolver:
    """
    A simple DPLL SAT solver implementation.
    https://www.philipzucker.com/smt_sat_solver2/

    >>> s = DPLLSolver()
    >>> x,y = s.makevar(), s.makevar()
    >>> s.clauses.append([x])
    >>> s.check()
    sat
    >>> s.model()
    {1: True}
    >>> s.clauses.append([-x])
    >>> s.check()
    unsat
    """

    trail: list[list[Var]] = field(default_factory=list)
    _model: list[Optional[bool]] = field(
        default_factory=lambda: [None]
    )  # Mapping from Var to value in current partial model. var0 unused because -0 = 0
    clauses: list[Clause] = field(default_factory=list)

    def makevar(self):
        vid = len(self._model)
        self._model.append(None)
        return vid

    def model(self):
        return {
            v: val for v, val in enumerate(self._model) if v != 0 and val is not None
        }

    def eval_lit(self, lit: Lit) -> Optional[bool]:
        "Find value of lit in current _model"
        val = self._model[abs(lit)]
        if val is None:
            return None
        return val if lit > 0 else not val

    def propagate(self) -> bool:
        "Find clauses with a single unassigned lit and make it true in the model"
        changed = False
        while changed:
            changed = False
            for clause in self.clauses:
                if any(self.eval_lit(lit) for lit in clause):
                    continue
                else:
                    unassigned = [lit for lit in clause if self.eval_lit(lit) is None]
                    if len(unassigned) == 0:
                        return True  # conflict
                    elif len(unassigned) == 1:
                        unit = unassigned[0]
                        print("propagate", unit)
                        v = abs(unit)
                        self._model[v] = unit > 0
                        self.trail[-1].append(v)
                        changed = True
        return False

    def backtrack(self):
        "Backtrack to previous decision level. Returns True if no more levels to backtrack to."
        if not self.trail:
            return True
        cur = self.trail.pop()
        while len(cur) > 1:
            v = cur.pop()
            self._model[v] = None
        v = cur.pop()
        if self._model[v]:
            self._model[v] = False  # try false after true
            cur.append(v)
            self.trail.append(cur)
            return False
        else:
            # We've already tried true and false
            self._model[v] = None
            return self.backtrack()

    def is_conflict(self) -> bool:
        for clause in self.clauses:
            if all(self.eval_lit(lit) is False for lit in clause):
                return True
        return False

    def is_sat(self) -> bool:
        for clause in (
            self.clauses
        ):  # I guess this could be a giant comprehension. harder to read probably.
            if any(self.eval_lit(lit) is True for lit in clause):
                continue
            else:
                return False
        return True

    def decide(self):
        "Pick first unassigned variable and assign it True. Make new decision level in trail"
        # TODO: Better decision heuristics
        for v in range(1, len(self._model)):
            if self._model[v] is None:
                self._model[v] = True
                self.trail.append([v])  # start new trail level
                return
        else:
            raise Exception("No unassigned variables to decide")

    def check(self):
        "DPLL loop. return True for sat, False for unsat"
        while True:
            self.propagate()
            if self.is_conflict():
                if self.backtrack():
                    return smt.unsat
            elif self.is_sat():
                return smt.sat
            else:
                self.decide()
