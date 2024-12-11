import kdrag.smt as smt
import lark

grammar = r"""
    start: _statement*

    _statement: fact
             | rule
             | query

    fact: predicate "."
    rule: predicate ":-" predicate_list "."
    query: "?-" predicate_list "."

    predicate_list: predicate ("," predicate)* // inlined

    predicate: IDENTIFIER "(" term_list? ")"
    term_list: term ("," term)* // inlined

    term: IDENTIFIER    -> const          // constants or functors
        | VARIABLE      -> var          // variables
        | IDENTIFIER "(" term_list ")" -> fun_app  // recursive terms (e.g., s(X))

    VARIABLE: /[A-Z][A-Za-z0-9_]*/  // Variables start with uppercase
    IDENTIFIER: /[a-z][A-Za-z0-9_]*/  // Constants and function names start with lowercase

    %import common.WS
    %ignore WS
"""

Term = smt.DeclareSort("Term")


def interp_term(t):
    token = t.data
    if token == "const":
        return smt.Const(t.children[0], Term)
    elif token == "var":
        return smt.Const(t.children[0], Term)
    elif token == "fun_app":
        args = t.children[1].children
        sortlist = [Term] * (len(args) + 1)
        f = smt.Function(t.children[0], *sortlist)
        return f(*[interp_term(a) for a in args])
    else:
        raise ValueError(f"Unexpected term {t}")


def interp_pred(t):
    assert t.data == "predicate"
    name = t.children[0]
    args = [interp_term(a) for a in t.children[1].children]
    return smt.Function(name, *([Term] * len(args)), smt.BoolSort())(*args)


def interp(t):
    assert t.data == "start"
    clauses = []
    for stmt in t.children:
        if stmt.data == "fact":
            clauses.append(interp_pred(stmt.children[0]))
        elif stmt.data == "rule":
            head = interp_pred(stmt.children[0])
            predlist = stmt.children[1]

            assert predlist.data == "predicate_list"
            body = [
                interp_pred(p) for p in [stmt.children[0]] + stmt.children[1].children
            ]
            clauses.append(smt.Implies(smt.And(*body), head))
        elif stmt.data == "query":
            q = [interp_pred(p) for p in stmt.children[0].children]
            print("query", q)
        else:
            raise ValueError(f"Unexpected statement {stmt}")
    return clauses


parser = lark.Lark(grammar, start="start", parser="lalr")
