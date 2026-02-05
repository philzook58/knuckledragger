import dd.autoref
import kdrag.smt as smt
import operator
import functools
import kdrag as kd


class BDD:
    """
    >>> x,y,z = smt.Bools('x y z')
    >>> bdd = BDD()
    >>> bdd.declare(x,y,z)
    >>> bdd.declare(z)
    >>> bdd.translate(smt.And(x, smt.Or(z, y))).count()
    3
    >>> bdd.translate(smt.Exists([y], smt.And(x, smt.Or(z, y)))).count()
    1
    >>> list(bdd.pick_iter(smt.Exists([y], smt.And(x, smt.Or(z, y)))))
    [[(x, True)]]
    """

    def __init__(self):
        self.bdd = dd.autoref.BDD()

    def declare(self, *vs: smt.ExprRef):
        for v in vs:
            assert (
                isinstance(v, smt.BoolRef)
                and v.sort() == smt.BoolSort()
                and smt.is_const(v)
            )
            self.bdd.declare(v.decl().name())

    def pick_iter(self, expr: smt.BoolRef):
        bdd_expr = self.translate(expr)
        for assignment in self.bdd.pick_iter(bdd_expr):
            yield [(smt.Bool(k), v) for k, v in assignment.items()]

    def pick(
        self, expr: smt.BoolRef, care_vars: list[smt.ExprRef]
    ) -> list[tuple[smt.BoolRef, bool]] | None:
        bdd_expr = self.translate(expr)
        assignment = self.bdd.pick(
            bdd_expr, care_vars={str(v.decl().name()) for v in care_vars}
        )
        if assignment is None:
            return None
        else:
            return [(smt.Bool(k), v) for k, v in assignment.items()]

    def substitute(self, e: smt.BoolRef, *substs) -> dd.autoref.Function:
        e1 = self.translate(e)
        substs = {v.decl().name(): self.translate(s) for v, s in substs}
        return self.bdd.let(substs, e1)

    def translate(self, expr: smt.BoolRef) -> dd.autoref.Function:
        memo: dict[int, dd.autoref.Function] = {}

        def worker(e):
            id_ = e.get_id()
            if id_ in memo:
                return memo[id_]
            elif smt.is_and(expr):
                res = functools.reduce(
                    operator.and_, [self.translate(a) for a in expr.children()]
                )
            elif smt.is_or(expr):
                res = functools.reduce(
                    operator.or_, [self.translate(a) for a in expr.children()]
                )
            elif smt.is_not(expr):
                res = ~self.translate(expr.arg(0))
            elif isinstance(expr, smt.QuantifierRef):
                vs, body = kd.utils.open_binder_unhygienic(expr)
                assert isinstance(body, smt.BoolRef)
                if expr.is_forall():
                    res = self.bdd.forall(
                        [v.decl().name() for v in vs], self.translate(body)
                    )
                elif expr.is_exists():
                    res = self.bdd.exist(
                        [v.decl().name() for v in vs], self.translate(body)
                    )
                else:
                    raise Exception("Unknown quantifier type", expr)
            elif smt.is_true(expr):
                res = self.bdd.true
            elif smt.is_false(expr):
                res = self.bdd.false
            elif smt.is_const(expr):
                assert isinstance(expr, smt.BoolRef) and expr.sort() == smt.BoolSort()
                # self.bdd.declare(expr.decl().name())
                res = self.bdd.var(expr.decl().name())
            else:
                raise Exception("Cannot translate to BDD", expr)
            memo[id_] = res
            return res

        return worker(expr)
