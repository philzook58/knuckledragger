import egglog.bindings as eggbnd
import kdrag as kd
import kdrag.smt as smt
import kdrag.solvers as solvers

# https://www.philipzucker.com/egglog_z3_simp/

solvers.collect_decls


def mangle_name(name):
    return name  # name.split("!"name.replace("!", "_bang_")


def z3_to_egglog(e: smt.ExprRef, vars=[]):
    """a simple sexpr traversal, but we wrap 0-arity constants in parens and vars in no parens to match egglog's syntax"""
    if any(e.eq(v) for v in vars):
        return mangle_name(e.sexpr())
    elif smt.is_const(e):
        return f"({mangle_name(e.decl().name())})"
    else:
        head, args = e.decl(), e.children()
        return f"({mangle_name(head.name())} {' '.join(z3_to_egglog(a, vars) for a in args)})"


class EgglogSolver:
    # TODO. Many other things are predefined
    predefined_names = ["=", "=>", "and", "or", "not", "true", "false"]

    def __init__(self, debug=False):
        self.egraph = eggbnd.EGraph()
        self.sorts = set()
        self.decls = set()
        self.debug = debug
        self.cmds = []

    def run_cmd(self, cmd: str):
        self.cmds.append(cmd)
        if self.debug:
            print(cmd)
        commands = self.egraph.parse_program(cmd)
        return self.egraph.run_program(*commands)

    def print_decl(self, decl: smt.FuncDeclRef, n: int):
        return self.run_cmd(f"(print-function {mangle_name(decl.name())} {n})")

    def add(self, thm: kd.Proof | smt.BoolRef | list[smt.BoolRef | kd.Proof]):
        """

        >>> s = EgglogSolver()
        >>> x, y = smt.Ints("x y")
        >>> add = smt.Function("add", smt.IntSort(), smt.IntSort(), smt.IntSort())
        >>> s.add(smt.ForAll([x, y], add(x,y) == add(y, x)))
        >>> res = s.run(5)

        >>> s = EgglogSolver()
        >>> V = smt.DeclareSort("V")
        >>> x, y, z = smt.Consts("x y z", V)
        >>> edge = smt.Function("edge", V, V, smt.BoolSort())
        >>> path = smt.Function("path", V, V, smt.BoolSort())
        >>> s.add(smt.ForAll([x, y], edge(x,y), path(x,y)))
        >>> s.add(smt.ForAll([x, y, z], path(x,y), edge(y,z), path(x,z)))
        >>> s.add(edge(x,y))
        >>> s.add(edge(y,z))
        >>> _ = s.run(10)
        >>> _ = s.run_cmd("(print-function path 100)")
        """
        if isinstance(thm, list):
            rules = [t.thm if isinstance(t, kd.Proof) else t for t in thm]
        elif isinstance(thm, kd.Proof):
            rules = [thm.thm]
        else:
            rules = [thm]
        for sort in solvers.collect_sorts(rules):
            if sort not in self.sorts:
                self.run_cmd(f"(sort {sort.name()})")
                self.sorts.add(sort)
        for decl in solvers.collect_decls(rules):
            if decl not in self.decls and decl.name() not in self.predefined_names:
                dom = " ".join([decl.domain(i).name() for i in range(decl.arity())])
                cmd = f"(constructor {decl.name()} ({dom}) {decl.range().name()})"
                self.run_cmd(cmd)
                self.decls.add(decl)
        for rule in rules:
            if (rw := kd.rewrite.rewrite_of_expr_exact(rule)) is not None:
                cmd = f"(rewrite {z3_to_egglog(rw.lhs, vars=rw.vs)} {z3_to_egglog(rw.rhs, vars=rw.vs)})"
                self.run_cmd(cmd)
            elif (clause := kd.rewrite.rule_of_expr_exact(rule)) is not None:
                vs, hyp, conc = clause.vs, clause.hyp, clause.conc
                if smt.is_and(hyp):
                    hyps = hyp.children()
                else:
                    hyps = [hyp]
                if smt.is_and(conc):
                    concs = conc.children()
                else:
                    concs = [conc]
                concs = [
                    f"(union {z3_to_egglog(c.arg(0), vars=vs)} {z3_to_egglog(c.arg(1), vars=vs)})"
                    if smt.is_eq(c)
                    else z3_to_egglog(c, vars=vs)
                    for c in concs
                ]
                cmd = f"(rule ({' '.join(z3_to_egglog(h, vars=clause.vs) for h in hyps)}) ({' '.join(concs)}))"
                self.run_cmd(cmd)
            elif smt.is_eq(rule):
                lhs, rhs = rule.children()
                cmd = f"(union {z3_to_egglog(lhs)} {z3_to_egglog(rhs)})"
                self.run_cmd(cmd)
            else:
                cmd = f"{z3_to_egglog(rule)}"
                self.run_cmd(cmd)

    def run(self, n):
        return self.run_cmd(f"(run {n})")

    def extract(self, goal: smt.ExprRef):
        return self.run_cmd(f"(extract {z3_to_egglog(goal)})")

    def let(self, name, expr):
        return self.run_cmd(f"(let {name} {z3_to_egglog(expr)})")


# TODO MaudeSolver
