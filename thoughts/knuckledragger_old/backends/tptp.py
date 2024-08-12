from smt import *


def smt_to_tptp(expr):
    if isinstance(expr, BoolRef):
        if expr.decl().kind() == smt_OP_TRUE:
            return "$true"
        if expr.decl().kind() == smt_OP_FALSE:
            return "$false"
        if expr.decl().kind() == smt_OP_AND:
            return "({})".format(" & ".join([z3_to_tptp(x) for x in expr.children()]))
        if expr.decl().kind() == smt_OP_OR:
            return "({})".format(" | ".join([z3_to_tptp(x) for x in expr.children()]))
        if expr.decl().kind() == smt_OP_NOT:
            return "~({})".format(z3_to_tptp(expr.children()[0]))
        if expr.decl().kind() == smt_OP_IMPLIES:
            return "({} => {})".format(
                smt_to_tptp(expr.children()[0]), smt_to_tptp(expr.children()[1])
            )
        if expr.decl().kind() == smt_OP_EQ:
            return "({} = {})".format(
                smt_to_tptp(expr.children()[0]), smt_to_tptp(expr.children()[1])
            )
        if expr.decl().kind() == smt_OP_DISTINCT:
            return "({} != {})".format(
                smt_to_tptp(expr.children()[0]), smt_to_tptp(expr.children()[1])
            )
        if expr.decl().kind() == smt_OP_ITE:
            return "ite({}, {}, {})".format(
                smt_to_tptp(expr.children()[0]),
                smt_to_tptp(expr.children()[1]),
                smt_to_tptp(expr.children()[2]),
            )
        if expr.decl().kind() == smt_OP_LE:
            return "({} <= {})".format(
                smt_to_tptp(expr.children()[0]), smt_to_tptp(expr.children()[1])
            )
        if expr.decl().kind() == smt_OP_GE:
            return "({} >= {})".format(
                smt_to_tptp(expr.children()[0]), smt_to_tptp(expr.children()[1])
            )
        if expr.decl().kind() == smt_OP_LT:
            return "({} < {})".format(
                smt_to_tptp(expr.children()[0]), smt_to_tptp(expr.children()[1])
            )
        if expr.decl().kind() == smt_OP_GT:
            return "({} > {})".format(z3_to_tptp)
        if expr.decl().kind() == smt_OP_ADD:
            return "({} + {})".format(
                smt_to_tptp(expr.children()[0]), smt_to_tptp(expr.children()[1])
            )
        if expr.decl().kind() == smt_OP_SUB:
            return "({} - {})".format(
                smt_to_tptp(expr.children()[0]), smt_to_tptp(expr.children()[1])
            )
        if expr.decl().kind() == smt_OP_MUL:
            return "({} * {})".format(
                smt_to_tptp(expr.children()[0]), smt_to_tptp(expr.children()[1])
            )
        else:
            assert False
    else:
        assert False





class TPTPProver(ProofDB):
    def __init__(self, binpath):
        self.binpath = binpath
    def infer(hyps: List[Theorem], conc: Term, command=None, timeout=1000) -> Term:
        for hyp in hyps:
            check(hyp)
            s.add(hyp[1])
        s.add(Not(conc))
        # TODO use better temporary file
        with open("/tmp/temp.smt2", "w") as f:
            f.write(s.sexpr())
        command.append("/tmp/temp.smt2")
        print(s.sexpr())
        res = subprocess.run(
            ["vampire", "--output_mode", "smtcomp"],
            timeout=1.0,
            capture_output=True,
        )
        print(res)
        if "unsat" not in res.stdout.decode("utf-8"):
            print(res.stdout.decode("utf-8"))
            assert False
        return trust(conc)

    def assume(self, formula):
        self.solver.add(formula)

    def prove(self, formula):
        self.solver.add(Not(formula))
        return self.solver.check() == unsat

    def __repr__(self):
        return f"TPTPProver({self.solver})"

    def __str__(self):
        return repr(self)

