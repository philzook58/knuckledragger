import kdrag as kd
import kdrag.smt as smt
import lark
import kdrag.rewrite as rw
from typing import Sequence
import sys

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


def interp_term(t: lark.Tree) -> smt.ExprRef:
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


def interp_pred(t: lark.Tree) -> smt.BoolRef:
    assert t.data == "predicate"
    name = t.children[0]
    args = [interp_term(a) for a in t.children[1].children]
    return smt.Function(name, *([Term] * len(args)), smt.BoolSort())(*args)


def get_vars(e: smt.ExprRef) -> list[smt.ExprRef]:
    todo = [e]
    res = set()
    while todo:
        e = todo.pop()
        if smt.is_const(e) and e.decl().name()[0].isupper():
            res.add(e)
        elif smt.is_app(e):
            todo.extend(e.children())
        else:
            raise ValueError(f"Unexpected expression {e}")
    return list(res)


def interp(
    t: lark.Tree,
) -> tuple[
    list[smt.BoolRef | smt.QuantifierRef],
    list[tuple[list[smt.ExprRef], list[smt.BoolRef]]],
]:
    assert t.data == "start"
    clauses = []
    queries = []
    for stmt in t.children:
        if stmt.data == "fact":
            e = interp_pred(stmt.children[0])
            vs = get_vars(e)
            if len(vs) == 0:
                clauses.append(interp_pred(stmt.children[0]))
            else:
                clauses.append(smt.ForAll(vs, e))
        elif stmt.data == "rule":
            head = interp_pred(stmt.children[0])
            predlist = stmt.children[1]
            assert predlist.data == "predicate_list"
            body = [interp_pred(p) for p in stmt.children[1].children]
            vs = list(set(get_vars(head)) | set().union(*(get_vars(p) for p in body)))
            if len(vs) == 0:
                clauses.append(smt.Implies(smt.And(*body), head))
            else:
                clauses.append(kd.QForAll(vs, smt.And(*body), head))
        elif stmt.data == "query":
            goals = [interp_pred(p) for p in stmt.children[0].children]
            vs = list(set().union(*(get_vars(g) for g in goals)))
            queries.append((vs, goals))
        else:
            raise ValueError(f"Unexpected statement {stmt}")
    return clauses, queries


parser = lark.Lark(grammar, start="start", parser="lalr")


def prolog(
    vs0: list[smt.ExprRef],
    goals: list[smt.BoolRef],
    rules0: Sequence[rw.Rule | smt.QuantifierRef | smt.BoolRef],
):
    """
    A small prolog interpreter. THis is a generator of solutions consisting of variable list, substitution pairs.

    >>> import kdrag.theories.nat as nat
    >>> x,y,z = smt.Consts("x y z", nat.Nat)
    >>> plus = smt.Function("plus", nat.Nat, nat.Nat, nat.Nat, smt.BoolSort())
    >>> rules = [\
        kd.QForAll([y], plus(nat.Z, y, y)),\
        kd.QForAll([x,y,z], smt.Implies(\
            plus(x, y, z),\
            plus(nat.S(x), y, nat.S(z))\
        ))]
    >>> list(prolog([x,y], [plus(x, y, nat.S(nat.Z))], rules))
    [([], {y: S(Z), x: Z}), ([], {x: S(Z), y: Z})]
    """
    rules = [
        rule if isinstance(rule, rw.Rule) else rw.rule_of_expr(rule)
        for rule in reversed(rules0)
    ]
    todo = [(vs0, goals, {})]
    while todo:
        vs, goals, subst = todo.pop()
        if len(goals) == 0:
            yield vs, {k: t for k, t in subst.items() if any(k.eq(v) for v in vs0)}
            continue
        else:
            goal = goals.pop()
            if smt.is_true(goal):
                todo.append((vs, goals, subst))
            elif smt.is_false(goal):
                continue
            elif smt.is_and(goal):
                goals.extend(reversed(goal.children()))
                todo.append((vs, goals, subst))
            elif smt.is_or(goal):
                for child in goal.children():
                    newgoals = goals + [child]
                    todo.append((vs, newgoals, subst))
            else:
                for rule in rules:
                    rule = rule.freshen()
                    vs1 = vs + rule.vs
                    subst1 = kd.utils.unify(vs1, rule.conc, goal)
                    if subst1 is None:
                        continue
                    else:
                        newgoals = goals + [smt.substitute(rule.hyp, *subst1.items())]
                        newsubst = {
                            **{
                                k: smt.substitute(v, *subst1.items())
                                for k, v in subst.items()
                            },
                            **subst1,
                        }
                        newvs = list(set(vs1) - set(subst1.keys()))
                        todo.append((newvs, newgoals, newsubst))


def run_string(s: str):
    """
    Run a Prolog-like string and return the results.

    >>> run_string("plus(z, Y, Y). plus(s(X), Y, s(Z)) :- plus(X, Y, Z). ?- plus(X, Y, s(z)).")
    [([], {Y: s(z), X: z}), ([], {X: s(z), Y: z})]
    """
    tree = parser.parse(s)
    clauses, queries = interp(tree)
    for vs, goals in queries:
        if len(goals) == 0:
            continue
        return list(prolog(vs, goals, clauses))


if __name__ == "__main__":
    with open(sys.argv[1]) as f:
        print(run_string(f.read()))
