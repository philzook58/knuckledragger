import kdrag.smt as smt
import kdrag as kd


def mangle_decl(d: smt.FuncDeclRef, env=[]):
    """Mangle a declaration to a tptp name. SMTLib supports type based overloading, TPTP does not."""
    # single quoted (for operators) + underscore + hex id
    id_, name = d.get_id(), d.name()
    name = name.replace("!", "bang")
    # TODO: mangling of operators is busted
    # name = name.replace("*", "star")
    assert id_ >= 0x80000000
    if d in env:
        return name + "_" + format(id_ - 0x80000000, "x")
    else:
        return name + "_" + format(id_ - 0x80000000, "x")
        # TODO: single quote is not working.
        # return "'" + d.name() + "_" + format(id_ - 0x80000000, "x") + "'"


def expr_to_cnf(expr: smt.BoolRef) -> str:
    """
    Print in CNF format.
    Will recognize a single ForAll(, Or(Not(...))) layer.

    >>> x = smt.Int("x")
    >>> y = smt.Int("y")
    >>> expr_to_cnf(smt.ForAll([x, y], smt.Or(x == y, x + 1 <= y)))
    '(X = Y) | <=(+(X, 1), Y)'
    """
    if isinstance(expr, smt.QuantifierRef):
        if not expr.is_forall():
            raise Exception("CNF conversion only supports universal quantification")
        vs, body = kd.utils.open_binder_unhygienic(expr)
        body = smt.substitute(
            body, *[(v, smt.Const(v.decl().name().upper(), v.sort())) for v in vs]
        )
    else:
        vs = []
        body = expr
    if smt.is_or(body):
        lits = body.children()
    else:
        lits = [body]

    def term(e: smt.ExprRef) -> str:
        if smt.is_const(e):
            return str(e)
        elif smt.is_app(e):
            args = [term(c) for c in e.children()]
            return f"{e.decl().name()}({', '.join(args)})"
        else:
            raise Exception("Unexpected term in CNF", e)

    def eq(e: smt.BoolRef) -> str:
        if smt.is_eq(e):
            return f"({term(e.arg(0))} = {term(e.arg(1))})"
        else:
            return term(e)

    def neg(e: smt.BoolRef) -> str:
        if smt.is_not(e):
            return f"~{eq(e.arg(0))}"
        else:
            return eq(e)

    return " | ".join([neg(l) for l in lits])


def expr_to_tptp(
    expr: smt.ExprRef, env=None, format="thf", theories=True, no_mangle=None
) -> str:
    """Pretty print expr as TPTP"""
    if env is None:
        env = []
    if no_mangle is None:
        no_mangle = set()
    if isinstance(expr, smt.IntNumRef):
        return str(expr.as_string())
    elif isinstance(expr, smt.QuantifierRef):
        vars, body = kd.utils.open_binder(expr)
        vdecls = [v.decl() for v in vars]
        env = env + vdecls
        no_mangle.update(vdecls)
        body = expr_to_tptp(
            body, env=env, format=format, theories=theories, no_mangle=no_mangle
        )
        if format == "fof":
            vs = ", ".join([v.decl().name().replace("!", "__") for v in vars])
            # type_preds = " & ".join(
            #    [
            #        f"{sort_to_tptp(v.sort())}({mangle_decl(v.decl(), env)}))"
            #        for v in vars
            #    ]
            # )
        else:
            vs = ", ".join(
                [
                    v.decl().name().replace("!", "__") + ":" + sort_to_tptp(v.sort())
                    for v in vars
                ]
            )
        if expr.is_forall():
            if format == "fof":
                # TODO: is adding type predicates necessary?
                # return f"(![{vs}] : ({type_preds}) => {body})"
                return f"(![{vs}] : {body})"
            return f"(![{vs}] : {body})"
        elif expr.is_exists():
            if format == "fof":
                # return f"(?[{vs}] : ({type_preds}) & {body})"
                return f"(?[{vs}] : {body})"
            return f"(?[{vs}] : {body})"
        elif expr.is_lambda():
            if format != "thf":
                raise Exception(
                    "Lambda not supported in tff tptp format. Try a thf solver", expr
                )
            return f"(^[{vs}] : {body})"
    assert smt.is_app(expr)
    children = [
        expr_to_tptp(c, env=env, format=format, theories=theories, no_mangle=no_mangle)
        for c in expr.children()
    ]
    decl = expr.decl()
    head = decl.name()
    if head == "true":
        return "$true"
    elif head == "false":
        return "$false"
    elif head == "and":
        return "({})".format(" & ".join(children))
    elif head == "or":
        return "({})".format(" | ".join(children))
    elif head == "=":
        return "({} = {})".format(children[0], children[1])
    elif head == "=>":
        return "({} => {})".format(children[0], children[1])
    elif head == "not":
        return "~({})".format(children[0])
    elif head == "if":
        # if thf:
        #    return "($ite @ {} @ {} @ {})".format(*children)
        # else:
        return "$ite({}, {}, {})".format(*children)
    elif head == "select":
        assert format == "thf"
        return "({} @ {})".format(*children)
    elif head == "distinct":
        if len(children) == 2:
            return "({} != {})".format(*children)
        return "$distinct({})".format(", ".join(children))

    if theories:
        if head == "<":
            return "$less({},{})".format(*children)
        elif head == "<=":
            return "$lesseq({},{})".format(*children)
        elif head == ">":
            return "$greater({},{})".format(*children)
        elif head == ">=":
            return "$greatereq({},{})".format(*children)
        elif head == "+":
            return "$sum({},{})".format(*children)
        elif head == "-":
            if len(children) == 1:
                return "$difference(0,{})".format(children[0])
            else:
                return "$difference({},{})".format(*children)
        elif head == "*":
            return "$product({},{})".format(*children)
        elif head == "/":
            return "$quotient({},{})".format(*children)
        # elif head == "^":
        #    return "$power({},{})".format(
        #        *children
        #    )  # This is not a built in tptp function though
    # default assume regular term

    if decl in no_mangle:
        head = decl.name().replace("!", "__")
    else:
        head = mangle_decl(decl, env)
    if len(children) == 0:
        return head
    if format == "thf":
        return f"({head} @ {' @ '.join(children)})"
    else:
        return f"{head}({', '.join(children)})"


def sort_to_tptp(sort: smt.SortRef):
    """Pretty print sort as tptp"""
    name = sort.name()
    if name == "Int":
        return "$int"
    elif name == "Bool":
        return "$o"
    elif name == "Real":
        return "$real"
    elif isinstance(sort, smt.ArraySortRef):
        return "({} > {})".format(
            sort_to_tptp(sort.domain()), sort_to_tptp(sort.range())
        )
    else:
        return name.lower()
