import lark
import kdrag.smt as smt
from lark import Tree

grammar = r"""
start: expr

?expr: quantifier
?quantifier: implication  | "forall" binders "," expr  -> forall_ | "exists" binders "," expr -> exists_ | "fun" binders "=>" expr -> fun_
?implication: disjunction | disjunction "->" implication  -> implies
?disjunction: conjunction | disjunction ("\\/" | "||") conjunction  -> or_
?conjunction: comparison  | conjunction ("/\\" | "&&") comparison  -> and_
?comparison: additive
    | comparison ("=" | "==") additive   -> eq  
    | comparison "!=" additive  -> neq
    | comparison "<" additive   -> lt  
    | comparison ">" additive   -> gt
    | comparison "<=" additive  -> le  
    | comparison ">=" additive  -> ge
?additive: multiplicative
    | additive "+" multiplicative  -> add | additive "-" multiplicative  -> sub
?multiplicative: application
    | multiplicative "*" application  -> mul | multiplicative "/" application  -> div
?application: atom atom* -> app
?atom: const | num | bool_ | "(" expr ")"

binders: binder+
binder: "(" NAME+ ":" sort ")"
?sort: arrow
?arrow: sortatom | sortatom "->" arrow -> array
?sortatom : NAME -> sortlit | "BitVec" NUMBER -> bitvecsort | "(" sort ")"

const: NAME
num: NUMBER
bool_: "true" | "false"

NAME: /[a-zA-Z_][a-zA-Z0-9_']*/
NUMBER: /-?\d+/
%import common.WS
%ignore WS
COMMENT: "--" /[^\n]*/
%ignore COMMENT
"""

parser = lark.Lark(grammar, start="start", parser="lalr")


def parse(s: str, globals=None) -> smt.ExprRef:
    """
    Parse a logical expression into an SMT expression.

    >>> parse("x + 1", {"x": smt.Int("x")})
    x + 1
    >>> x, y = smt.Ints("x y")
    >>> assert parse("forall (x y : Int), x + 1 = 0 -> x = -1").eq( smt.ForAll([x, y], x + 1 == 0, x == -1))
    >>> a = smt.Real("a")
    >>> assert parse("exists (a : Real), a * a = 2").eq(smt.Exists([a], a * a == 2))
    >>> parse("fun (x : Int -> Int) => x 1 = 2")
    Lambda(x, x[1] == 2)
    >>> parse("fun (x : Int -> Int -> Int) => x 1 3 = 2")
    Lambda(x, x[1][3] == 2)
    >>> parse("f 3 2", {"f": smt.Function("f", smt.IntSort(), smt.IntSort(), smt.IntSort())})
    f(3, 2)
    >>> parse("fun (x : Int) (y : Real) => x + y > 0")
    Lambda([x, y], ToReal(x) + y > 0)
    >>> parse(r"forall (x : Int), x >= 0 /\\ x < 10")
    ForAll(x, And(x >= 0, x < 10))
    >>> parse(r"forall (x : Int), x >= 0 && x < 10 -> x < 20")
    ForAll(x, Implies(And(x >= 0, x < 10), x < 20))
    >>> parse(r"exists (x : (BitVec 32) -> BitVec 8), x 8 = 5")
    Exists(x, x[8] == 5)
    """
    env = {}

    def lookup(name) -> smt.AstRef:
        if name in env:
            res = env[name]
        elif globals is not None and name in globals:
            res = globals[name]
        else:
            raise ValueError("Unknown name", name)
        assert isinstance(res, smt.AstRef)
        return res

    def sort(tree) -> smt.SortRef:
        match tree:
            case Tree("array", [left, right]):
                return smt.ArraySort(sort(left), sort(right))
                # return smt.ArraySort(*(sort(s) for s in left.children), sort(right))
            case Tree("bitvecsort", [n]):
                n1 = int(n)  # type: ignore
                return smt.BitVecSort(n1)
            case Tree("sortlit", [name]):
                if name == "Int":
                    return smt.IntSort()
                elif name == "Real":
                    return smt.RealSort()
                elif name == "Bool":
                    return smt.BoolSort()
                else:
                    s = lookup(name)
                    if isinstance(s, smt.SortRef):
                        return s
                    else:
                        raise ValueError("Name is not a sort", name, s)
            case _:
                raise ValueError("Unknown sort tree", tree)

    def binder(tree) -> list[smt.ExprRef]:
        match tree:
            case Tree("binder", names_sort):
                names = names_sort[:-1]
                s = sort(names_sort[-1])
                return [smt.Const(str(name), s) for name in names]
            case _:
                raise ValueError("Unknown binder tree", tree)

    def binders(tree) -> list[smt.ExprRef]:
        match tree:
            case Tree("binders", bs):
                return [v for b in bs for v in binder(b)]
            case _:
                raise ValueError("Unknown binders tree", tree)

    def quant(vs, body_tree, q) -> smt.QuantifierRef:
        nonlocal env
        old_env = env.copy()
        vs = binders(vs)
        for v in vs:
            env[str(v)] = v
        res = q(vs, expr(body_tree))
        env = old_env
        return res

    def expr(tree) -> smt.ExprRef:
        match tree:
            # TODO: obviously this is not well typed.
            case Tree("num", [n]):
                return int(n)  # type: ignore
            case Tree("const", [name]):
                res = lookup(name)  # type: ignore
                return res  # type: ignore
            case Tree("and_", [left, right]):
                return smt.And(expr(left), expr(right))
            case Tree("or_", [left, right]):
                return smt.Or(expr(left), expr(right))
            case Tree("add", [left, right]):
                return expr(left) + expr(right)
            case Tree("sub", [left, right]):
                return expr(left) - expr(right)
            case Tree("mul", [left, right]):
                return expr(left) * expr(right)
            case Tree("div", [left, right]):
                return expr(left) / expr(right)
            case Tree("eq", [left, right]):
                return smt.Eq(expr(left), expr(right))
            case Tree("le", [left, right]):
                return expr(left) <= expr(right)
            case Tree("lt", [left, right]):
                return expr(left) < expr(right)
            case Tree("ge", [left, right]):
                return expr(left) >= expr(right)
            case Tree("gt", [left, right]):
                return expr(left) > expr(right)
            case Tree("app", [func]):  # constant
                return expr(func)
            case Tree("app", [func, *args]):
                # auto curry
                args = [expr(arg) for arg in args]
                func = expr(func)
                if isinstance(func, smt.FuncDeclRef):
                    return func(*args)
                elif smt.is_func(func):
                    while args:
                        assert isinstance(func, smt.QuantifierRef) or isinstance(
                            func, smt.ArrayRef
                        )
                        doms = smt.domains(func)
                        func = func[*args[: len(doms)]]
                        args = args[len(doms) :]
                    return func
                else:
                    raise ValueError("Cannot apply non-function", func)
            case Tree("forall_", [vs, body]):
                return quant(vs, body, smt.ForAll)
            case Tree("exists_", [vs, body]):
                return quant(vs, body, smt.Exists)
            case Tree("fun_", [vs, body]):
                return quant(vs, body, smt.Lambda)
            case Tree("implies", [left, right]):
                return smt.Implies(expr(left), expr(right))
            case _:
                raise ValueError("Unknown parse tree", tree)

    tree = parser.parse(s)
    match tree:
        case Tree("start", [e]):
            res = expr(e)
            assert isinstance(res, smt.ExprRef)
            return res
        case _:
            raise ValueError("Invalid parse tree", tree)
