import egglog.bindings as eggbnd
import kdrag as kd
import kdrag.smt as smt
import kdrag.solvers as solvers

# https://www.philipzucker.com/egglog_z3_simp/

solvers.collect_decls


def mangle_name(name):
    return name.replace("!", "_bang_")


def z3_to_egglog(e: smt.ExprRef, vars=[]):
    """a simple sexpr traversal, but we wrap 0-arity constants in parens and vars in no parens to match egglog's syntax"""
    if e in vars:
        return mangle_name(e.sexpr())
    else:
        head, args = e.decl(), e.children()
        return f"({mangle_name(head.name())} {' '.join(z3_to_egglog(a, vars) for a in args)})"


class EgglogSolver(solvers.BaseSolver):
    # TODO. Many other things are predefined
    predefined_names = ["="]

    def __init__(self, debug=False):
        self.egraph = eggbnd.EGraph()
        self.sorts = set()
        self.decls = set()
        self.debug = debug

    def run_cmd(self, cmd: str):
        if self.debug:
            print(cmd)
        commands = self.egraph.parse_program(cmd)
        return self.egraph.run_program(*commands)

    def add(self, thm: smt.ExprRef):
        rule = thm
        for sort in solvers.collect_sorts([rule]):
            if sort not in self.sorts:
                self.run_cmd(f"(sort {sort.name()})")
                self.sorts.add(sort)
        for decl in solvers.collect_decls([rule]):
            if decl not in self.decls and decl.name() not in self.predefined_names:
                dom = " ".join([decl.domain(i).name() for i in range(decl.arity())])
                cmd = f"(constructor {decl.name()} ({dom}) {decl.range().name()})"
                self.run_cmd(cmd)
                self.decls.add(decl)
        if isinstance(rule, smt.QuantifierRef):
            assert rule.is_forall()
            vs, r = kd.utils.open_binder(rule)
            if r.decl().name() != "=":
                raise ValueError("Only equality rules are supported", rule)
            lhs, rhs = r.children()
            cmd = f"(rewrite {z3_to_egglog(lhs,vars=vs)} {z3_to_egglog(rhs, vars=vs)})"
            self.run_cmd(cmd)
        else:
            if rule.decl().name() != "=":
                raise ValueError("Only equality rules are supported", rule)
            lhs, rhs = rule.children()
            cmd = f"(union {z3_to_egglog(lhs)} {z3_to_egglog(rhs)})"
            self.run_cmd(cmd)

    def run(self, n):
        return self.run_cmd(f"(run {n})")

    def extract(self, goal: smt.ExprRef):
        return self.run_cmd(f"(extract {z3_to_egglog(goal)})")

    def let(self, name, expr):
        return self.run_cmd(f"(let {name} {z3_to_egglog(expr)})")


# TODO MaudeSolver
