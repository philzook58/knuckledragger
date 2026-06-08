import scryer
import kdrag.smt as smt
from kdrag.printers.tptp import expr_to_tptp, expr_to_cnf


Term = scryer.Term
Var = scryer.Term.Var
Atom = scryer.Term.Atom
Compound = scryer.Term.Compound
List = scryer.Term.List


tptp_prelude = r"""
% TPTP syntax
:- op(1130, xfy, <~>).  % negated equivalence
:- op(1110, xfy, <=).   % implication
:- op(1100, xfy, '|').  % disjunction
:- op(1100, xfy, '~|'). % negated disjunction
:- op(1000, xfy, &).    % conjunction
:- op(1000, xfy, ~&).   % negated conjunction
:- op( 500, fy, !).     % universal quantifier
:- op( 500, fy, ?).     % existential quantifier
:- op( 400, xfx, =).    % equality
:- op( 300, xf, !).     % negated equality (for !=) Very annoying
:- op( 299, fx, $).     % for $true/$false
"""


def _from_scryer(
    term: scryer.Term, decls: dict[str, smt.FuncDeclRef], vars, sort=None
) -> smt.ExprRef:
    match term:
        case Var(name):
            if name in vars:
                if sort is not None:
                    assert vars[name].sort() == sort
                return vars[name]
            else:
                assert sort is not None, f"Variable sort is not inferrable {name}"
                v = smt.Const(name, sort)
                vars[name] = v
                return v
        case Atom(name):
            if name in decls:
                return decls[name]()
            else:
                assert sort is not None
                return smt.Const(name, sort)
        case Compound("=", [Compound("!", [lhs]), rhs]):
            lhs = _from_scryer(lhs, decls, vars)
            return smt.Distinct(lhs, _from_scryer(rhs, decls, vars, sort=lhs.sort()))
        case Compound("$", [t]):
            match t:
                case Atom("true"):
                    return smt.BoolVal(True)
                case Atom("false"):
                    return smt.BoolVal(False)
                case _:
                    raise Exception(f"Untranslatable term: {term}")
        case Compound(name, args):
            if name == "=":
                assert len(args) == 2
                lhs = _from_scryer(args[0], decls, vars)
                return smt.Eq(lhs, _from_scryer(args[1], decls, vars, sort=lhs.sort()))
            if name in decls:
                decl = decls[name]
                args = [
                    _from_scryer(arg, decls, vars, sort=decl.domain(i))
                    for i, arg in enumerate(args)
                ]
                return decl(*args)
            else:
                raise Exception(f"Untranslatable term: {term}")
        case _:
            raise Exception(f"Unsupported constructor: {term}")
        # case scryer.Term.List(values):


def from_scryer(
    term: scryer.Term, decls: dict[str, smt.FuncDeclRef]
) -> tuple[list[smt.ExprRef], smt.ExprRef]:
    """
    Translate a scryer term to a z3 expression.

    >>> x,y = smt.Ints("x y")
    >>> decls = {"f": smt.Function("f", smt.IntSort(), smt.IntSort())}
    >>> from_scryer(Compound("f", [Var("x")]), decls)
    ([x], f(x))
    >>> from_scryer(Compound("=", [Compound("f", [Var("x")]), Var("y")]), decls)
    ([x, y], f(x) == y)
    """
    vars = {}
    res = _from_scryer(term, decls, vars)
    return list(vars.values()), res


def to_term(vs: list[smt.ExprRef], expr: smt.ExprRef) -> scryer.Term:
    """
    >>> x,y = smt.Ints("x y")
    >>> str(to_term([], x + y))
    '+(x, y)'
    """
    if smt.is_const(expr):
        if any(expr.eq(v) for v in vs):
            return Var(str(expr))
        return Atom(str(expr))
    elif smt.is_app(expr):
        args = [to_term(vs, c) for c in expr.children()]
        return Compound(expr.decl().name(), args)
    else:
        raise Exception("Unexpected term", expr)


def to_scryer_str(expr: smt.BoolRef) -> str:
    return expr_to_cnf(expr)


def subterms(term: scryer.Term) -> set[scryer.Term]:
    res = set()
    todo = [term]
    while todo:
        term = todo.pop()
        res.add(term)
        if isinstance(term, Compound):
            todo.extend(term.args)
        elif isinstance(term, List):
            todo.extend(term.values)
    return res


def in_term(term: scryer.Term, tags: set[scryer.Term]) -> set[scryer.Term]:
    todo = [term]
    res = set()
    while todo:
        term = todo.pop()
        if term in tags:
            res.add(term)
        if isinstance(term, Compound):
            todo.extend(term.args)
        elif isinstance(term, List):
            todo.extend(term.values)
    return res
