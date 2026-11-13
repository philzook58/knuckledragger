"""Built-in infix notation shared by the Lean and display printers."""

from kdrag import smt


# Lean precedence and associativity from Init.Notation. Arrow binds below Or.
_LEAN_INFIX = (
    {
        smt.Z3_OP_IMPLIES: ("→", 25, "right"),
        smt.Z3_OP_OR: ("∨", 30, "right"),
        smt.Z3_OP_AND: ("∧", 35, "right"),
        smt.Z3_OP_EQ: ("=", 50, "none"),
        smt.Z3_OP_LT: ("<", 50, "none"),
        smt.Z3_OP_LE: ("≤", 50, "none"),
        smt.Z3_OP_GT: (">", 50, "none"),
        smt.Z3_OP_GE: ("≥", 50, "none"),
        smt.Z3_OP_ADD: ("+", 65, "left"),
        smt.Z3_OP_SUB: ("-", 65, "left"),
        smt.Z3_OP_MUL: ("*", 70, "left"),
    }
    if smt.solver == smt.Z3SOLVER
    else {}
)
