"""
A parser for a simple logical expression language using Lark. The syntax is inspired by Lean's

Unicode symbols are not required, but if you like them, adding the Unicode LaTeX extension for VSCode
https://marketplace.visualstudio.com/items?itemName=oijaz.unicode-latex
Goto the `File > Preferences > Settings` of the plugin and add `python` to the enabled extensions.
Reloading your window will enable access via backslash autocomplete commands.
For example \\alpha will tab autocomplete to α.
"""

import lark
import kdrag.smt as smt
from lark import Tree
import kdrag as kd
from typing import NamedTuple

grammar = r"""
start: expr

?expr: ite
?ite: quantifier | "if" expr "then" expr "else" expr -> if
?quantifier: implication  | ("forall" | "∀") binders "," expr  -> forall_ | \
    ("exists" | "∃") binders "," expr -> exists_ | ("fun" | "λ") binders ("=>" | "↦") expr -> fun_ | set
?implication: disjunction | disjunction ("->" | "→") implication  -> implies
?disjunction: conjunction | disjunction ("\\/" | "∨" | "||" | "∪" ) conjunction  -> or_
?conjunction: comparison  | conjunction ("/\\" | "∧" | "&&" | "∩") comparison  -> and_
?comparison: additive
    | comparison ("=" | "==") additive   -> eq  
    | comparison "!=" additive  -> neq
    | comparison ("<" | "⊂") additive   -> lt  
    | comparison (">" | "⊃") additive   -> gt
    | comparison ("<=" | "≤" | "⊆") additive  -> le  
    | comparison (">=" | "≥" | "⊇") additive  -> ge
?additive: multiplicative
    | additive "+" multiplicative  -> add | additive "-" multiplicative  -> sub
?multiplicative: application
    | multiplicative "*" application  -> mul | multiplicative "/" application  -> div
?application: atom atom* -> app
?atom: const | num | bool_ | "(" expr ")" | seq

binders: binder+ | NAME ":" sort -> sing_binder
?binder: "(" NAME+ ":" sort ")" -> annot_binder | NAME -> infer_binder
?sort: arrow
?arrow: sortatom | sortatom ("->" | "→") arrow -> array
?sortatom : NAME -> sortlit | "BitVec" NUMBER -> bitvecsort | "(" sort ")" | "'" NAME -> typevar

const: NAME ("." NAME)*
num: NUMBER
bool_: ("true" | "True") -> true | ("false" | "False") -> false
seq  : "[" expr ("," expr)* "]"

set : "{" binders "|" expr "}"


inductive: "inductive" NAME "where" ("|" constructor)+
constructor: NAME ":" (sortatom ("->" | "→"))* NAME

define: "def" NAME binders ":" sort ":=" expr

axiom : "axiom" NAME ":" expr

theorem : "theorem" NAME ":" expr ":=" "grind"

NAME: /[a-zA-Z_][a-zA-Z0-9_']*/
NUMBER: /-?\d+/
%import common.WS
%ignore WS
COMMENT: "--" /[^\n]*/
%ignore COMMENT
"""

parser = lark.Lark(grammar, start="start", parser="lalr")


class Env(NamedTuple):
    locals: dict
    globals: dict

    def __getitem__(self, key):
        if key in self.locals:
            return self.locals[key]
        elif key in self.globals:
            return self.globals[key]
        else:
            raise KeyError(key)

    def __setitem__(self, key, value):
        self.locals[key] = value

    def copy(self):
        return Env(self.locals.copy(), self.globals)


def sort(tree: Tree, env: Env) -> smt.SortRef:
    match tree:
        case Tree("array", [left, right]):
            return smt.ArraySort(sort(left, env), sort(right, env))
            # return smt.ArraySort(*(sort(s) for s in left.children), sort(right,env))
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
            elif name == "Prop":  # bad idea?
                return smt.BoolSort()
            elif name == "String":
                return smt.StringSort()
            elif name == "Unit":
                return kd.UnitSort()
            else:
                s = env[name]
                if isinstance(s, smt.SortRef):
                    return s
                else:
                    raise ValueError("Name is not a sort", name, s)
        case Tree("typevar", [name]):
            return smt.DeclareTypeVar(str(name))
        case _:
            raise ValueError("Unknown sort tree", tree)


def binder(tree, env) -> list[smt.ExprRef]:
    match tree:
        case Tree("annot_binder", names_sort):
            names = names_sort[:-1]
            s = sort(names_sort[-1], env)
            return [smt.Const(str(name), s) for name in names]
        case Tree(
            "infer_binder", [name]
        ):  # TODO: This is a bit goofy, but does match how z3py works.
            v = env[name]
            if isinstance(v, smt.ExprRef) and smt.is_const(v):
                return [v]
            else:
                raise ValueError("Inferred binder is not a constant", name, v)
        case _:
            raise ValueError("Unknown binder tree", tree)


def binders(tree, env) -> list[smt.ExprRef]:
    match tree:
        case Tree("binders", bs):
            return [v for b in bs for v in binder(b, env)]
        case Tree("sing_binder", [name, sort_tree]):
            s = sort(sort_tree, env)
            return [smt.Const(str(name), s)]
        case _:
            raise ValueError("Unknown binders tree", tree)


def quant(vs, body_tree, q, env) -> smt.QuantifierRef:
    env = env.copy()
    vs = binders(vs, env)
    for v in vs:
        env[str(v)] = v
    res = q(vs, expr(body_tree, env))
    return res


def expr(tree, env: Env) -> smt.ExprRef:
    match tree:
        # TODO: obviously this is not well typed.
        case Tree("num", [n]):
            return int(n)  # type: ignore
        case Tree("const", [name, *attrs]):
            res = env[name]  # type: ignore
            for attr in attrs:
                res = getattr(res, str(attr))  # type: ignore
            return res  # type: ignore
        case Tree("true", []):
            return smt.BoolVal(True)
        case Tree("false", []):
            return smt.BoolVal(False)
        case Tree("seq", items):
            return smt.Concat(*[smt.Unit(expr(item, env)) for item in items])
        case Tree("and_", [left, right]):
            return smt.And(expr(left, env), expr(right, env))
        case Tree("or_", [left, right]):
            return smt.Or(expr(left, env), expr(right, env))
        case Tree("add", [left, right]):
            return expr(left, env) + expr(right, env)
        case Tree("sub", [left, right]):
            return expr(left, env) - expr(right, env)
        case Tree("mul", [left, right]):
            return expr(left, env) * expr(right, env)
        case Tree("div", [left, right]):
            return expr(left, env) / expr(right, env)
        case Tree("eq", [left, right]):
            return smt.Eq(expr(left, env), expr(right, env))
        case Tree("neq", [left, right]):
            return expr(left, env) != expr(right, env)  # type: ignore
        case Tree("le", [left, right]):
            return expr(left, env) <= expr(right, env)
        case Tree("lt", [left, right]):
            return expr(left, env) < expr(right, env)
        case Tree("ge", [left, right]):
            return expr(left, env) >= expr(right, env)
        case Tree("gt", [left, right]):
            return expr(left, env) > expr(right, env)
        case Tree("app", [func]):  # constant
            return expr(func, env)
        case Tree("app", [func, *args]):
            # auto curry
            args = [expr(arg, env) for arg in args]
            func = expr(func, env)
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
            return quant(vs, body, smt.ForAll, env)
        case Tree("exists_", [vs, body]):
            return quant(vs, body, smt.Exists, env)
        case Tree("fun_", [vs, body]):
            return quant(vs, body, smt.Lambda, env)
        case Tree("set", [vs, body]):
            t = quant(vs, body, smt.Lambda, env)
            if t.sort().range() != smt.BoolSort():
                raise ValueError("Set comprehension must return Bool", t)
            return t
        case Tree("if", [cond, then_, else_]):
            return smt.If(expr(cond, env), expr(then_, env), expr(else_, env))
        case Tree("implies", [left, right]):
            return smt.Implies(expr(left, env), expr(right, env))
        case _:
            raise ValueError("Unknown parse tree", tree)


def start(tree: lark.Tree, globals) -> smt.ExprRef:
    env = Env(locals={}, globals=globals)
    match tree:
        case Tree("start", [e]):
            res = expr(e, env)
            assert res is not None
            return res
        case _:
            raise ValueError("Invalid parse tree", tree)


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
    >>> parse("fun x y (z : Int) => x + y + z", {"x": smt.Int("x"), "y": smt.Int("y")})
    Lambda([x, y, z], x + y + z)
    >>> parse("fun (x : 'a) => x").sort()
    Array(a, a)
    >>> parse("true")
    True
    >>> parse("[true, false]")
    Concat(Unit(True), Unit(False))
    >>> q = smt.Const("x", smt.TupleSort("pair", [smt.IntSort(), smt.BoolSort()])[0])
    >>> parse("q.project1", {"q": q})
    project1(x)
    >>> parse("{x : Int | x > 0}")
    Lambda(x, x > 0)
    >>> parse("if true && false then 1 + 1 else 0")
    If(And(True, False), 2, 0)
    """
    return start(parser.parse(s), globals)


def lean(s: str, globals=None) -> smt.ExprRef:
    """
    Alias for parse to match Lean users' expectations.

    >>> foo = smt.Int("foo1")
    >>> lean("foo + 2")
    foo1 + 2
    """
    if globals is None:
        _, globals = kd.utils.calling_globals_locals()
    return parse(s, globals)


inductive_parser = lark.Lark(grammar, start="inductive", parser="lalr")


def inductive_of_tree(tree: lark.Tree, globals=None) -> smt.DatatypeSortRef:
    """
    Parse an inductive datatype definition.

    >>> tree = inductive_parser.parse("inductive nat where | zero : nat | succ : nat -> nat | fiz : Int -> Bool -> (Bool -> nat) -> nat")
    >>> inductive_of_tree(tree).constructor(1)
    succ
    >>> inductive_of_tree(tree).accessor(1,0)
    succ0
    """
    if globals is None:
        _, globals = kd.utils.calling_globals_locals()
    match tree:
        case Tree("inductive", [name, *constructors]):
            dt = kd.Inductive(str(name))
            env = Env(locals={str(name): smt.DatatypeSort(name)}, globals=globals or {})
            for cons in constructors:
                match cons:
                    case Tree("constructor", [cons_name, *sorts, self_name]):
                        if str(self_name) != str(name):
                            raise ValueError(
                                "Inductive constructor return type does not match",
                                self_name,
                                name,
                            )
                        dt.declare(str(cons_name), *[sort(t, env) for t in sorts])
                    case _:
                        raise ValueError("Unknown constructor tree", cons)
            return dt.create()
        case _:
            raise ValueError("Unexpected lark.Tree in inductive", tree)


# todo: allow dot const in sorts.
def inductive(s: str, globals=None) -> smt.DatatypeSortRef:
    """
    Parse an inductive datatype definition.

    >>> inductive("inductive boollist where | nil : boollist | cons : Bool -> boollist -> boollist").constructor(0)
    nil
    >>> Nat = kd.Nat
    >>> inductive("inductive foo where | mkfoo : Nat -> foo")
    foo
    """
    if globals is None:
        _, globals = kd.utils.calling_globals_locals()
    tree = inductive_parser.parse(s)
    return inductive_of_tree(tree, globals)


def define(tree: lark.Tree, env: Env) -> smt.FuncDeclRef:
    """
    Parse a definition.

    >>> tree = lark.Lark(grammar, start="define", parser="lalr").parse("def add1 (x : Int) : Int := x + 1")
    >>> define(tree, Env(locals={}, globals={})).defn
    |= ForAll(x, add1(x) == x + 1)
    """
    match tree:
        case Tree("define", [name, binds, sort_tree, body]):
            env = env.copy()
            vs = binders(binds, env)
            for v in vs:
                env[str(v)] = v
            s = sort(sort_tree, env)
            f = smt.Function(str(name), *[v.sort() for v in vs], s)
            env[str(name)] = f
            body = expr(body, env)
            return kd.define(str(name), vs, body)
        case _:
            raise ValueError("Unexpected lark.Tree in define", tree)


def axiom(tree: lark.Tree, env: Env) -> kd.kernel.Proof:
    """
    Parse an axiom.

    >>> tree = lark.Lark(grammar, start="axiom", parser="lalr").parse("axiom add1_nonneg : forall x : Int, x >= x - 1")
    >>> axiom(tree, Env(locals={}, globals={}))
    |= ForAll(x, x >= x - 1)
    """
    match tree:
        case Tree("axiom", [name, body]):
            body = expr(body, env)
            assert isinstance(body, smt.BoolRef)
            return kd.axiom(body, by=[str(name)])
        case _:
            raise ValueError("Unexpected lark.Tree in axiom", tree)


def theorem(tree: lark.Tree, env: Env) -> kd.kernel.Proof:
    """
    Parse a theorem.

    >>> tree = lark.Lark(grammar, start="theorem", parser="lalr").parse("theorem add1_nonneg : forall x : Int, x >= x - 1 := grind")
    >>> theorem(tree, Env(locals={}, globals={}))
    |= ForAll(x, x >= x - 1)
    """
    match tree:
        case Tree("theorem", [_name, body]):
            body = expr(body, env)
            assert isinstance(body, smt.BoolRef)
            return kd.Lemma(body).qed()
        case _:
            raise ValueError("Unexpected lark.Tree in theorem", tree)
