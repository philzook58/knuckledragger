from z3 import *


def expr2tptp(expr):
    if isinstance(expr, BoolRef):
        if expr.decl().kind() == Z3_OP_TRUE:
            return "$true"
        if expr.decl().kind() == Z3_OP_FALSE:
            return "$false"
        if expr.decl().kind() == Z3_OP_AND:
            return "({})".format(" & ".join([expr2tptp(x) for x in expr.children()]))
        if expr.decl().kind() == Z3_OP_OR:
            return "({})".format(" | ".join([expr2tptp(x) for x in expr.children()]))
        if expr.decl().kind() == Z3_OP_NOT:
            return "~({})".format(expr2tptp(expr.children()[0]))
        if expr.decl().kind() == Z3_OP_IMPLIES:
            return "({} => {})".format(
                expr2tptp(expr.children()[0]), expr2tptp(expr.children()[1])
            )
        if expr.decl().kind() == Z3_OP_EQ:
            return "({} = {})".format(
                expr2tptp(expr.children()[0]), expr2tptp(expr.children()[1])
            )
        if expr.decl().kind() == Z3_OP_DISTINCT:
            return "({} != {})".format(
                expr2tptp(expr.children()[0]), expr2tptp(expr.children()[1])
            )
        if expr.decl().kind() == Z3_OP_ITE:
            return "ite({}, {}, {})".format(
                expr2tptp(expr.children()[0]),
                expr2tptp(expr.children()[1]),
                expr2tptp(expr.children()[2]),
            )
        if expr.decl().kind() == Z3_OP_LE:
            return "({} <= {})".format(
                expr2tptp(expr.children()[0]), expr2tptp(expr.children()[1])
            )
        if expr.decl().kind() == Z3_OP_GE:
            return "({} >= {})".format(
                expr2tptp(expr.children()[0]), expr2tptp(expr.children()[1])
            )
        if expr.decl().kind() == Z3_OP_LT:
            return "({} < {})".format(
                expr2tptp(expr.children()[0]), expr2tptp(expr.children()[1])
            )
        if expr.decl().kind() == Z3_OP_GT:
            return "({} > {})".format(expr2tptp)
        if expr.decl().kind() == Z3_OP_ADD:
            return "({} + {})".format(
                expr2tptp(expr.children()[0]), expr2tptp(expr.children()[1])
            )
        if expr.decl().kind() == Z3_OP_SUB:
            return "({} - {})".format(
                expr2tptp(expr.children()[0]), expr2tptp(expr.children()[1])
            )
        if expr.decl().kind() == Z3_OP_MUL:
            return "({} * {})".format(
                expr2tptp(expr.children()[0]), expr2tptp(expr.children()[1])
            )
        else:
            assert False
    else:
        assert False
