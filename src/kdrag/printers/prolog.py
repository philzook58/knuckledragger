import kdrag.smt as smt
import kdrag as kd


def to_prolog(vs: list[smt.ExprRef], expr: smt.ExprRef) -> str:
    """

    >>> x,y = smt.Ints("x y")
    >>> to_prolog([x,y], smt.Or(x == 0, x == y))
    '((X = 0) ; (X = Y))'
    """
    # TODO: try to recognize CLP constraints
    # TODO: sequences as lists

    if isinstance(expr, smt.QuantifierRef):
        # I guess I could support harrop? Lambda? a to_prolog_goal, to_prolog_prog
        raise Exception(
            "Quantifiers not supported in prolog, use kd.utils.open_binder first", expr
        )
    elif smt.is_int_value(expr):
        assert isinstance(expr, smt.IntNumRef)
        return str(expr.as_long())
    elif smt.is_const(expr):
        if any(expr.eq(v) for v in vs):
            return str(expr).upper()
        name = str(expr.decl().name())
        if name.isupper():
            raise Exception(
                "Prolog does not allow constants starting with uppercase letters", expr
            )
        return name
    elif smt.is_app(expr):
        args = [to_prolog(vs, c) for c in expr.children()]
        if smt.is_implies(expr):
            return f"({args[1]} :- {args[0]})"
        elif smt.is_or(expr):
            return "(" + " ; ".join(args) + ")"
        elif smt.is_and(expr):
            return " , ".join([to_prolog(vs, c) for c in expr.children()])
        elif smt.is_eq(expr):
            return f"({to_prolog(vs, expr.arg(0))} = {to_prolog(vs, expr.arg(1))})"
        elif smt.is_distinct(expr):
            assert len(expr.children()) == 2
            return f"dif({to_prolog(vs, expr.arg(0))},{to_prolog(vs, expr.arg(1))})"
        elif smt.is_add(expr):
            args = [to_prolog(vs, c) for c in expr.children()]
            return "(" + " + ".join(args) + ")"
        elif smt.is_mul(expr):
            args = [to_prolog(vs, c) for c in expr.children()]
            return "(" + " * ".join(args) + ")"
        elif smt.is_if(expr):
            # declarative if?
            return f"{to_prolog(vs, expr.arg(1))} -> {to_prolog(vs, expr.arg(0))} ; {to_prolog(vs, expr.arg(2))}"
        elif smt.is_le(expr):
            return f"({to_prolog(vs, expr.arg(0))} #=< {to_prolog(vs, expr.arg(1))})"
        elif smt.is_lt(expr):
            return f"({to_prolog(vs, expr.arg(0))} #< {to_prolog(vs, expr.arg(1))})"
        return f"{expr.decl().name()}({', '.join(args)})"
    else:
        raise Exception("Unexpected expression type in to_prolog", expr)


def to_clause(e: smt.BoolRef) -> str:
    """
    >>> x,y = smt.Ints("x y")
    >>> to_clause(smt.ForAll([x, y], smt.Or(x == y, x + 1 <= y)))
     '((X = Y) ; ((X + 1) #=< Y)).'
    """
    if isinstance(e, smt.QuantifierRef):
        if not e.is_forall():
            raise Exception("Only universal quantification supported in to_clause", e)
        vs0, body = kd.utils.open_binder_unhygienic(e)
        vs = [smt.Const(v.decl().name().upper(), v.sort()) for v in vs0]
        assert kd.utils.free_in(vs, body)
        body = smt.substitute(body, *zip(vs0, vs))
    else:
        vs = []
        body = e
    return to_prolog(vs, body) + "."
