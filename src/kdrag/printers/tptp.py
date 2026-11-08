import kdrag.smt as smt
import kdrag as kd
import re
from z3 import is_app_of, Z3_OP_UNINTERPRETED, Z3_OP_DT_RECOGNISER


def identifier(name: str) -> str:
    """The portable user-name convention: lowercase initial, no punctuation."""
    if not re.fullmatch(r"[a-z][A-Za-z0-9_]*", name) or name.startswith("kd_"):
        raise ValueError(
            f"Non-portable TPTP name {name!r}; use a lowercase initial and letters, digits or underscores (e.g. vec3_add); kd_ is reserved"
        )
    return name


def mangle_decl(d: smt.FuncDeclRef, env=None):
    """Keep user names unchanged; only generated symbols need generated names."""
    if env is not None and d in env:
        return env[d]
    if d.kind() == Z3_OP_DT_RECOGNISER:
        return "kd_is_" + identifier(d.params()[0].name())
    if re.fullmatch(r".*![0-9]+", d.name()):
        return f"kd_f_{d.get_id():x}"
    return identifier(d.name())


def validate_names(decls, sorts):
    names = {}
    for d in decls:
        name = mangle_decl(d)
        if name in names and names[name] != d:
            raise ValueError(
                f"TPTP overloading is forbidden: {name!r} names both {names[name].sexpr()} and {d.sexpr()}"
            )
        names[name] = d
    declarations = names
    names = {}
    for sort in sorts:
        name = sort_to_tptp(sort)
        if name in declarations:
            raise ValueError(f"TPTP sort/function name collision: {name!r}")
        if name in names and names[name] != sort:
            raise ValueError(
                f"TPTP sort-name collision: {names[name]} and {sort} both print as {name}"
            )
        names[name] = sort


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
        elif smt.is_distinct(e):
            assert len(e.children()) == 2
            return f"({term(e.arg(0))} != {term(e.arg(1))})"
        else:
            return term(e)

    def neg(e: smt.BoolRef) -> str:
        if smt.is_not(e):
            return f"~{eq(e.arg(0))}"
        else:
            return eq(e)

    return " | ".join([neg(l) for l in lits])


def cnf_file(axioms: list[smt.BoolRef], nnf=False) -> str:
    """
    Make a file out of a list of axioms in CNF format.
    Will recognize a single ForAll(, Or(Not(...))) layer.
    >>> x,y = smt.Ints("x y")
    >>> f = smt.Function("f", smt.IntSort(), smt.IntSort())
    >>> cnf_file([smt.ForAll([x, y], smt.Or(x == y, f(x) <= f(y)))])
    'cnf(0,axiom,(X = Y) | <=(f(X), f(Y))).'
    """
    if nnf:
        g = smt.Goal()
        g.add(axioms)
        g = smt.Tactic("nnf")(g)
        assert len(g) == 1
        axioms = g[0]
    res = []
    for i, axiom in enumerate(axioms):
        res.append(f"cnf({i},axiom,{expr_to_cnf(axiom)}).")
    return "\n".join(res)


def expr_to_tptp(expr: smt.ExprRef, env=None, format="thf", theories=True) -> str:
    """Pretty print expr as TPTP

    >>> x,y = smt.Ints("x y")
    >>> expr_to_tptp(smt.ForAll([x,y], smt.Implies(x < y, x + 1 <= y)))
    '(![V0:$int, V1:$int] : ($less(V0,V1) => $lesseq($sum(V0,1),V1)))'
    """
    if format == "cnf":
        assert isinstance(expr, smt.BoolRef)
        return expr_to_cnf(expr)
    if format not in ["thf", "tff", "fof"]:
        raise Exception(
            "Unsupported TPTP format",
            format,
            "Supported formats are cnf, thf, tff, fof",
        )
    if env is None:
        env = {}
    if isinstance(expr, smt.IntNumRef):
        return str(expr.as_string())
    elif isinstance(expr, smt.QuantifierRef):
        vars, body = kd.utils.open_binder(expr)
        vdecls = [v.decl() for v in vars]
        env = dict(env)
        offset = len(env)
        env.update((d, f"V{offset + i}") for i, d in enumerate(vdecls))
        body = expr_to_tptp(body, env=env, format=format, theories=theories)
        if format == "fof":
            vs = ", ".join([env[v.decl()] for v in vars])
            # type_preds = " & ".join(
            #    [
            #        f"{sort_to_tptp(v.sort())}({mangle_decl(v.decl(), env)}))"
            #        for v in vars
            #    ]
            # )
        else:
            vs = ", ".join([env[v.decl()] + ":" + sort_to_tptp(v.sort()) for v in vars])
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
        expr_to_tptp(c, env=env, format=format, theories=theories)
        for c in expr.children()
    ]
    decl = expr.decl()
    head = decl.name()
    if is_app_of(expr, Z3_OP_UNINTERPRETED):
        head = mangle_decl(decl, env)
        if not children:
            return head
        if format == "thf":
            return f"({head} @ {' @ '.join(children)})"
        return f"{head}({', '.join(children)})"
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
        if head == "to_real":
            return "$to_real({})".format(children[0])
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

    head = mangle_decl(decl, env)
    if len(children) == 0:
        return head
    if format == "thf":
        return f"({head} @ {' @ '.join(children)})"
    else:
        return f"{head}({', '.join(children)})"


def sort_to_tptp(sort: smt.SortRef):
    """Pretty print sort as tptp

    >>> sort_to_tptp(smt.IntSort())
    '$int'
    >>> sort_to_tptp(smt.ArraySort(smt.IntSort(), smt.BoolSort()))
    '($int > $o)'
    """
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
        return identifier(name.lower())
