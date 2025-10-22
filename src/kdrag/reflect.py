"""
Reflecting and reifying SMT expressions from/into Python values.
"""

import kdrag.smt as smt
import kdrag as kd
import typing
import fractions
import functools
from typing import Callable, no_type_check
from collections import namedtuple
import operator
from dataclasses import dataclass
import ast
import inspect


def sort_of_type(t: type) -> smt.SortRef:
    """
    Give equivalent SMT sort for a given Python type.


    >>> sort_of_type(int)
    Int
    >>> sort_of_type(list[int])
    Seq(Int)
    >>> sort_of_type(dict[str, int])
    Array(String, Int)

    """
    origin = typing.get_origin(t)

    if origin is None:
        if t is int:
            return smt.IntSort()
        elif t is fractions.Fraction:
            return smt.RealSort()
        elif t is bool:
            return smt.BoolSort()
        elif t is float:
            return smt.RealSort()  # Floats correspond to reals in SMT
        elif t is str:
            return smt.StringSort()
        # elif is_subclassof(t, NamedTuple):
        #    # Handle NamedTuple fields as a tuple sort
        #    fields = t._field_types  # Get fields and types from the NamedTuple
        #    return smt.TupleSort(*[sort_of_type(typ) for typ in fields.values()])
        else:
            raise NotImplementedError(f"Type {t} is not supported")
    else:
        # Handle generic types
        args = typing.get_args(t)
        if origin is list:
            if len(args) != 1:
                raise NotImplementedError("List must have exactly one type parameter")
            return smt.SeqSort(sort_of_type(args[0]))  # Lists as sequences
        # elif origin is tuple:
        #    return smt.TupleSort(*[sort_of_type(arg) for arg in args])
        elif origin is dict:
            if len(args) != 2:
                raise NotImplementedError("Dict must have exactly two type parameters")
            return smt.ArraySort(sort_of_type(args[0]), sort_of_type(args[1]))
        # elif origin == Union:
        #    return smt.DatatypeSortRef(*[sort_of_type(arg) for arg in args])
        else:
            raise NotImplementedError(f"Generic type {origin} is not supported")


def type_of_sort(s: smt.SortRef) -> type:
    """
    Give equivalent Python type for a given SMT sort.

    >>> type_of_sort(smt.IntSort())
    <class 'int'>
    >>> type_of_sort(smt.ArraySort(smt.StringSort(), smt.IntSort()))
    dict[str, int]
    >>> type_of_sort(smt.SeqSort(smt.IntSort()))
    list[int]
    """
    if s == smt.IntSort():
        return int
    elif s == smt.RealSort():
        return fractions.Fraction
    elif s == smt.BoolSort():
        return bool
    elif s == smt.StringSort():
        return str
    elif isinstance(s, smt.ArraySortRef):
        return dict[type_of_sort(s.domain()), type_of_sort(s.range())]
    elif isinstance(s, smt.SeqSortRef):
        return list[type_of_sort(s.basis())]
    else:
        raise NotImplementedError(f"Sort {s} is not supported")


@functools.cache
def namedtuple_of_constructor(sort: smt.DatatypeSortRef, idx: int):
    """
    Given a datatype sort and an index, return a named tuple with field names and the constructor.
    >>> Nat = smt.Datatype("Nat")
    >>> Nat.declare("Z")
    >>> Nat.declare("S", ("pred", Nat))
    >>> Nat = Nat.create()
    >>> namedtuple_of_constructor(Nat, 1)(0)
    S(pred=0)
    """
    decl = sort.constructor(idx)
    fields = [sort.accessor(idx, i).name() for i in range(decl.arity())]
    return namedtuple(decl.name(), fields)


@dataclass
class KnuckleClosure:
    """
    A closure that can be used to evaluate expressions in a given environment.
    We don't use lambda so that we can inspect
    """

    lam: smt.QuantifierRef
    globals: dict[str, object]
    locals: dict[str, object]
    default: Callable[[smt.ExprRef], object]

    def __call__(self, *args):
        # TODO: Should I open binder more eagerly before call?
        vs, body = kd.utils.open_binder(self.lam)
        return eval_(
            body,
            globals=self.globals,
            locals={
                **{v.decl().name(): arg for v, arg in zip(vs, args)},
                **self.locals,
            },
            default=self.default,
        )


def __default_error(e):
    raise ValueError(f"Cannot evaluate {e}")


# This is fiendishly difficult to typecheck probably
@no_type_check
def eval_(e: smt.ExprRef, globals={}, locals={}, default=__default_error):
    """
    Evaluate a z3 expression in a given environment. The analog of python's `eval`.

    >>> eval_(smt.IntVal(42))
    42
    >>> eval_(smt.IntVal(1) + smt.IntVal(2))
    3
    >>> x = smt.Int("x")
    >>> eval_(smt.Lambda([x], x + 1)[3])
    4
    >>> R = kd.Struct("R", ("x", kd.Z), ("y", smt.BoolSort()))
    >>> eval_(R(42, True).x)
    42
    >>> eval_(R(42,True).is_R)
    True
    """

    def worker(e, locals):
        if isinstance(e, smt.QuantifierRef):
            if e.is_lambda():
                # also possibly lookup Lambda in globals.
                """
                if "Lambda" in globals:
                    vs, body = open_binder(e)
                    return globals["Lambda"]
                """
                return KnuckleClosure(e, globals, locals, default)
            else:
                raise ValueError("Quantifier not implemented", e)
        elif isinstance(e, smt.IntNumRef):  # smt.is_int_value(e):
            return e.as_long()
        elif isinstance(e, smt.RatNumRef):
            return fractions.Fraction(e.numerator_as_long(), e.denominator_as_long())
        elif isinstance(e, smt.FPNumRef):
            raise ValueError("FPNumRef not implemented")
        elif smt.is_app(e):
            # Lazy evaluation of if, and, or, implies
            if smt.is_if(e):
                c = worker(e.arg(0), locals)
                if isinstance(c, bool):
                    if c:
                        return worker(e.arg(1), locals)
                    else:
                        return worker(e.arg(2), locals)
                elif "If" in globals:
                    return globals["If"](
                        c, worker(e.arg(1), locals), worker(e.arg(2), locals)
                    )
                elif isinstance(c, smt.ExprRef):
                    return smt.If(
                        c,
                        worker(e.arg(1), locals),
                        worker(e.arg(2), locals),
                    )
                else:
                    # TODO: possibly lookup "If" in environment?
                    raise ValueError("If condition not a boolean or expression", c)
            elif smt.is_and(e):
                acc = []
                for child in e.children():
                    echild = worker(child, locals)
                    if isinstance(echild, bool):
                        if echild:
                            continue
                        else:
                            return False
                    else:
                        acc.append(echild)
                if len(acc) == 0:
                    return True
                return functools.reduce(operator.and_, acc)
                # return smt.And(acc)
            elif smt.is_or(e):
                acc = []
                for child in e.children():
                    echild = worker(child, locals)
                    if echild is True:
                        return True
                    elif echild is False:
                        continue
                    else:
                        acc.append(echild)
                if len(acc) == 0:
                    return False
                return functools.reduce(operator.or_, acc)
                # return smt.Or(acc)  # TODO: possibly simplify or
            elif smt.is_implies(e):
                cond = worker(e.arg(0), locals)
                if isinstance(cond, bool):
                    if cond:
                        return worker(e.arg(1), locals)
                    else:
                        return True
                else:
                    return smt.Implies(
                        cond, worker(e.arg(1), locals)
                    )  # TODO: possibly simplify implies if consequent evaluates to a bool?
            # eval all children
            children = list(map(lambda x: worker(x, locals), e.children()))
            decl = e.decl()
            if decl in kd.kernel.defns:
                defn = kd.kernel.defns[e.decl()]
                # Fresh vars and add to context?
                # e1 = z3.substitute(defn.body, *zip(defn.args, e.children()))
                f = worker(smt.Lambda(defn.args, defn.body), locals)
                return f(*children)
                # return eval_(
                #    smt.Select(smt.Lambda(defn.args, defn.body), *children), globals=globals
                # )
                # return eval_(env, e1)
            elif decl.name() in locals:
                if smt.is_const(e):
                    return locals[decl.name()]
                else:
                    return locals[decl.name()](*children)
            elif decl.name() in globals:
                # hasattr(globals[decl.name()], "__call__")?
                if smt.is_const(e):
                    return globals[decl.name()]
                else:
                    return globals[decl.name()](*children)
            elif smt.is_accessor(e):
                # return children[0][decl.name()]
                return getattr(children[0], e.decl().name())
            elif smt.is_select(e):  # apply
                if isinstance(children[0], Callable):
                    return children[0](*children[1:])
                elif len(children) == 2:
                    return children[0][children[1]]
                else:
                    raise ValueError("Select not implemented", e)
            elif smt.is_store(e):
                raise ValueError("Store not implemented", e)
            #    #return children[0]._replace(children[1], children[2])
            elif smt.is_const_array(e):
                return lambda x: children[0]  # Maybe return a Closure here?
            elif smt.is_map(e):
                raise ValueError("Map not implemented", e)
                # return map(children[0], children[1])
            elif smt.is_constructor(e):
                sort, decl = e.sort(), e.decl()
                i = 0  # Can't have 0 constructors. Makes typechecker happy
                for i in range(sort.num_constructors()):
                    if e.decl() == sort.constructor(i):
                        break
                cons = namedtuple_of_constructor(sort, i)
                return cons(*children)
            elif isinstance(e, smt.BoolRef):
                if smt.is_true(e):
                    return True
                elif smt.is_false(e):
                    return False
                elif smt.is_not(e):
                    return ~children[0]
                elif smt.is_eq(e):
                    return children[0] == children[1]
                elif smt.is_lt(e):
                    return children[0] < children[1]
                elif smt.is_le(e):
                    return children[0] <= children[1]
                elif smt.is_ge(e):
                    return children[0] >= children[1]
                elif smt.is_gt(e):
                    return children[0] > children[1]
                elif smt.is_recognizer(e):
                    sort = e.arg(0).sort()
                    decl = e.decl()
                    name = None
                    for i in range(sort.num_constructors()):
                        if e.decl() == sort.recognizer(i):
                            name = sort.constructor(i).name()
                    assert name is not None
                    if type(children[0]).__name__ == name:
                        return True
                    else:
                        return False
                else:
                    return default(e)
            # elif smt.is_string_value(e):
            #    return e.as_string()
            # elif isisntance(e, ArithRef):
            elif smt.is_add(e):
                return functools.reduce(operator.add, children)
            elif smt.is_mul(e):
                return functools.reduce(operator.mul, children)
            elif smt.is_neg(e):
                return -children[0]
            elif smt.is_sub(e):
                return children[0] - children[1]
            elif smt.is_div(e):
                return children[0] / children[1]
            elif smt.is_idiv(e):
                return children[0] // children[1]
            elif smt.is_power(e):
                return children[0] ** children[1]
            elif smt.is_mod(e):
                return children[0] % children[1]
            else:
                # we could raise error, or just return the expression itself (object | ExprRef) semantics
                return default(e)
        else:
            return default(e)

    return worker(e, locals)


def reify(s: smt.SortRef, x: object) -> smt.ExprRef:
    """
    sort directed reification of a python value. https://en.wikipedia.org/wiki/Normalisation_by_evaluation
    >>> reify(smt.IntSort(), 42)
    42
    >>> reify(smt.IntSort(), 42).sort()
    Int
    >>> x = smt.Int("x")
    >>> kd.utils.alpha_eq(reify(smt.ArraySort(smt.IntSort(), smt.IntSort()), lambda x: x + 1), smt.Lambda([x], x + 1))
    True
    >>> reify(smt.RealSort(), fractions.Fraction(10,16))
    5/8
    """
    if isinstance(x, KnuckleClosure):
        return x.lam  # TODO: Do I need to substitute in the env? Probably. That stinks. recurse into subterms, find name matches, reify those out of env
    if isinstance(x, smt.ExprRef):
        if x.sort() != s:
            raise ValueError(f"Sort mismatch of {x} : {x.sort()} != {s}")
        return x  # Although if we deeply modelled smt inside smt, maybe we'd want to quote here.
    elif isinstance(s, smt.ArraySortRef):
        # TODO: Probably not right, also not dealing with multi arg lambdas.
        if isinstance(x, Callable):
            v = smt.FreshConst(s.domain())
            y = x(v)
            assert y.sort() == s.range()
            return smt.Lambda([v], y)
        else:
            raise ValueError(f"Cannot call {x} as an array sort {s}")
    elif isinstance(s, smt.DatatypeSortRef):
        if isinstance(x, tuple):
            for i in range(s.num_constructors()):
                decl = s.constructor(i)
                if decl.name() == type(x).__name__:
                    arity = decl.arity()
                    assert len(x) == arity
                    return decl(*[reify(decl.domain(j), x[j]) for j in range(arity)])
            raise ValueError(f"Cannot reify {x} as a datatype {s}")
        raise ValueError("Reification on datatypesort not yet implemented")
    elif s == smt.IntSort():
        return smt.IntVal(x)
    elif s == smt.RealSort():
        return smt.RealVal(x)
    elif s == smt.BoolSort():
        return smt.BoolVal(x)
    elif s == smt.StringSort():
        return smt.StringVal(x)
    else:
        raise ValueError(f"Cannot reify {x} as an expression")


def infer_sort(x: object) -> smt.SortRef:
    if isinstance(x, int):
        return smt.IntSort()
    elif isinstance(x, fractions.Fraction):
        return smt.RealSort()
    elif isinstance(x, bool):
        return smt.BoolSort()
    elif isinstance(x, str):
        return smt.StringSort()
    elif isinstance(x, list):
        assert len(x) > 0
        return smt.SeqSort(infer_sort(x[0]))
    elif isinstance(x, KnuckleClosure):
        return x.lam.sort()
    else:
        raise ValueError(f"Cannot infer sort of {x}")


def nbe(x: smt.ExprRef) -> smt.ExprRef:
    """
    Normalization by evaluation.

    >>> nbe(smt.IntVal(41) + smt.IntVal(1))
    42
    >>> x,y = smt.Ints("x y")
    >>> nbe(smt.Lambda([x], x + 1)[3])
    4
    >>> nbe(smt.Lambda([x], x + 1))
    Lambda(x, x + 1)
    >>> nbe(smt.Lambda([x], smt.IntVal(3) + 1))
    Lambda(x, 3 + 1)
    """
    return reify(x.sort(), eval_(x))


def _lookup(name, globals=None, locals=None):
    if locals is not None and name in locals:
        return locals[name]
    if globals is not None and name in globals:
        return globals[name]
    raise ValueError(f"Could not find {name} in global or local environment")


def _reflect_expr(expr: ast.expr, globals=None, locals=None) -> smt.ExprRef:
    def rec(expr: ast.expr) -> smt.ExprRef:
        match expr:
            case ast.Constant(value, kind=None):
                return smt._py2expr(value)
            # case ast.UnaryOp(ast.UAdd(), operand):
            #    return +rec(operand)
            case ast.UnaryOp(ast.Not(), operand):
                return ~rec(operand)  # type: ignore
            case ast.UnaryOp(ast.USub(), operand):
                return -rec(operand)  # type: ignore
            case ast.UnaryOp(ast.Invert(), operand):
                return ~rec(operand)  # type: ignore
            case ast.UnaryOp(_, operand):
                raise NotImplementedError(f"UnaryOp {expr.op}")
            case ast.BinOp(left=l, op=ast.Add(), right=r):
                return rec(l) + rec(r)  # type: ignore
            case ast.BinOp(left=l, op=ast.Sub(), right=r):
                return rec(l) - rec(r)  # type: ignore
            case ast.BinOp(left=l, op=ast.Mult(), right=r):
                return rec(l) * rec(r)  # type: ignore
            case ast.BinOp(left=l, op=ast.Div(), right=r):
                return rec(l) / rec(r)  # type: ignore
            case ast.BinOp(left=l, op=ast.Mod(), right=r):
                return rec(l) % rec(r)  # type: ignore
            case ast.BinOp(left=l, op=ast.Pow(), right=r):
                return rec(l) ** rec(r)  # type: ignore
            case ast.BinOp(left=l, op=ast.LShift(), right=r):
                return rec(l) << rec(r)  # type: ignore
            case ast.BinOp(left=l, op=ast.RShift(), right=r):
                return rec(l) >> rec(r)  # type: ignore
            case ast.BinOp(left=l, op=ast.BitOr(), right=r):
                return rec(l) | rec(r)  # type: ignore
            case ast.BinOp(left=l, op=ast.BitXor(), right=r):
                return rec(l) ^ rec(r)  # type: ignore
            case ast.BinOp(left=l, op=ast.BitAnd(), right=r):
                return rec(l) & rec(r)  # type: ignore
            case ast.BinOp(left=l, op=ast.FloorDiv(), right=r):
                return rec(l) // rec(r)  # type: ignore
            case ast.BoolOp(op=ast.And(), values=values):
                return smt.And(*map(rec, values))
            case ast.BoolOp(op=ast.Or(), values=values):
                return smt.Or(*map(rec, values))
            case ast.Compare(left, ops, rights):
                acc = []
                left = rec(left)
                for op, right in zip(ops, rights):
                    right = rec(right)
                    match op:
                        case ast.Eq():
                            acc.append(smt.Eq(left, right))
                        case ast.NotEq():
                            acc.append(left != right)
                        case ast.Lt():
                            acc.append(left < right)  # type: ignore
                        case ast.LtE():
                            acc.append(left <= right)  # type: ignore
                        case ast.Gt():
                            acc.append(left > right)  # type: ignore
                        case ast.GtE():
                            acc.append(left >= right)  # type: ignore
                        case _:
                            raise NotImplementedError(f"Compare {op}")
                    left = right
                if len(acc) > 1:
                    return smt.And(*acc)
                else:
                    return acc[0]
            case ast.Call(func, args, keywords):
                assert keywords == []
                f = rec(func)
                assert isinstance(f, Callable)
                return f(*map(rec, args))
            case ast.IfExp(test, body, orelse):
                return smt.If(rec(test), rec(body), rec(orelse))
            case ast.Name(id_, _ctx):
                return _lookup(id_, locals=locals, globals=globals)
            case ast.Attribute(value, attr, _ctx):
                return getattr(rec(value), attr)
            case x:
                raise ValueError(
                    "Could not interpret expression", ast.unparse(x), ast.dump(x)
                )

    return rec(expr)


def _calling_globals_locals():
    stack = inspect.stack()
    if len(stack) > 2:
        caller_frame = stack[2]
        frame = caller_frame.frame
        return frame.f_locals, frame.f_globals
    raise ValueError("No calling site found")


def expr(expr: str, globals=None, locals=None) -> smt.ExprRef:
    """
    Turn a string of a python expression into a z3 expressions.
    Globals are inferred to be current scope if not given.

    >>> expr("x + 1", globals={"x": smt.Int("x")})
    x + 1
    >>> x = smt.Int("x")
    >>> f = smt.Function("f", smt.IntSort(), smt.IntSort())
    >>> expr("f(x) + 1 if 0 < x < 5 < 7 else x * x")
    If(And(0 < x, 5 > x, 5 < 7), f(x) + 1, x*x)

    """
    if globals is None:
        globals, _ = _calling_globals_locals()
    return _reflect_expr(
        ast.parse(expr, mode="eval").body, globals=globals, locals=locals
    )


def _reflect_stmts(stmts: list[ast.stmt], globals=None, locals=None) -> smt.ExprRef:
    """
    Turn a list of python statements into a z3 Expression.

    This is a "purely functional" subset of python, with assignment treated as a `let`.

    It is possible to model more of python but that is not what this function is for. It works for a subset of python for which
    the behavior of the mathematical language of Knuckledragger and python coincide.

    A very restricted subset of python statements are allowed.
    It must be a sequence of simple assignments ended by a return or if statement.
    for loops, while loops are not allowed.
    """
    assert len(stmts) > 0
    if locals is None:
        locals = {}
    for stmt in stmts[:-1]:
        match stmt:
            case ast.Assign(targets=[ast.Name(id_, _ctx)], value=value):
                value = _reflect_expr(value, globals=globals, locals=locals)
                locals = {**locals, id_: value}
            case _:
                raise ValueError(f"Statement {stmt}")
    match stmts[-1]:
        case ast.Return(value=value):
            if value is None:
                raise ValueError("Returning None not allowed")
            return _reflect_expr(value, globals, locals)
        case ast.If(test, body, orelse):
            test = _reflect_expr(test, globals, locals)
            body = _reflect_stmts(body, globals, locals)
            orelse = _reflect_stmts(orelse, globals, locals)
            return smt.If(test, body, orelse)
        # Todo match.
        case _:
            raise ValueError(
                f"Statement {ast.dump(stmts[-1])} not supported as last statement. Must be a return or if"
            )


def _sort_of_annotation(ann, globals={}, locals={}):
    match ann:
        case ast.Name(id_):
            s = eval(id_, globals, locals)
            if isinstance(s, smt.SortRef):
                return s
            elif isinstance(s, type):
                return sort_of_type(s)
            # if id_ == "int":
            #    return smt.IntSort()
            else:
                raise NotImplementedError(f"Name {id_}")
        case ast.Constant(value):
            assert isinstance(value, str)
            s = eval(value.replace('"', ""), globals, locals)
            if isinstance(s, type):
                return sort_of_type(s)
            elif smt.is_func(s):
                raise NotImplementedError("Subsort types not yet supported")
            elif isinstance(s, smt.SortRef):
                return s
            else:
                raise ValueError(f"Constant {value} is not a supported type or sort")
        case _:
            raise NotImplementedError(f"Annotation {ast.dump(ann)}")


def reflect(f, globals=None) -> smt.FuncDeclRef:
    """
    Reflect a function definition by injecting the parameters and recursive self call into the local environment.
    Uses type annotations to do so.

    Only handles a purely functional subset of python.
    Simple assignment is handled as a `let` who's scope extends to the end of it's subbranch.
    Every branch must end with a return.

    You can still call original function under attribute `__wrapped__`.

    >>> def foo(x : int) -> int:
    ...     return x + 3
    >>> foo = reflect(foo)
    >>> foo.__wrapped__(3)
    6
    >>> foo.defn
    |= ForAll(x, foo(x) == x + 3)

    >>> @reflect
    ... def bar(x : int, y : str) -> int:
    ...     if x > 4:
    ...         return x + 3
    ...     elif y == "fred":
    ...        return 14
    ...     else:
    ...        return bar(x - 1, y)
    >>> bar.defn
    |= ForAll([x, y],
           bar(x, y) ==
           If(4 < x, x + 3, If(y == "fred", 14, bar(x - 1, y))))
    >>> @reflect
    ... def inc_7(n: "int") -> "int":
    ...    return n + 1
    >>> inc_7(6)
    inc_7(6)
    """
    module = ast.parse(inspect.getsource(f))
    assert isinstance(module, ast.Module) and len(module.body) == 1
    fun = module.body[0]
    assert isinstance(fun, ast.FunctionDef)
    assert len(fun.args.posonlyargs) == 0 and len(fun.args.kwonlyargs) == 0
    locals = {}
    if globals is None:
        globals, _ = _calling_globals_locals()
    # infer arguments from type annotations.
    args = []
    # We add arguments to locals in order to support dependent types.
    for arg in fun.args.args:
        v = smt.Const(
            arg.arg, _sort_of_annotation(arg.annotation, globals=globals, locals=locals)
        )
        args.append(v)
        locals[v.decl().name()] = v

    # args = [
    #    smt.Const(
    #        arg.arg, _sort_of_annotation(arg.annotation, locals=locals, globals=globals)
    #    )
    # ]
    if fun.returns is None:
        raise ValueError(f"Function {fun.name} must have a return type annotation")
    # insert self name into locals so that recursive calls work.
    z3fun = smt.Function(
        fun.name,
        *[arg.sort() for arg in args],
        _sort_of_annotation(fun.returns, globals=globals, locals=locals),
    )
    locals[fun.name] = z3fun
    # Actually interpret body.
    body = _reflect_stmts(fun.body, globals=globals, locals=locals)
    z3fun1 = kd.define(fun.name, args, body)
    # Check that types work out.
    if z3fun.range() != z3fun1.range():
        raise ValueError(
            f"Function {fun.name} has return type {_sort_of_annotation(fun.returns, globals=globals, locals=locals)} but body evaluates to {body.sort()}"
        )
    # This should never fail.
    assert z3fun.arity() == z3fun1.arity() and all(
        z3fun.domain(i) == z3fun1.domain(i) for i in range(z3fun.arity())
    )
    return functools.update_wrapper(z3fun1, f)  # type: ignore


def datatype(s: str, locals=None, globals=None) -> smt.DatatypeSortRef:
    """
    Use python type syntax to define an algebraic datatype datatype.
    Fields can be specified positionally or by name.
    Reads the inner types from current environment.

    >>> Int = smt.IntSort()
    >>> Real = smt.RealSort()
    >>> Foo = datatype("type Foo = Biz | Bar | Baz(Int, Int, smt.IntSort()) | Boz(x = Int, y = Int)")
    >>> Foo.Baz.domain(1)
    Int
    >>> Foo.x.range()
    Int
    """

    if locals is None or globals is None:
        frame = inspect.currentframe()
        if frame is None or frame.f_back is None:
            raise ValueError("No calling site found")
        f_back = frame.f_back
        locals = f_back.f_locals if locals is None else locals
        globals = f_back.f_globals if globals is None else globals
    mod = ast.parse(s)
    body = mod.body
    if len(body) != 1:
        raise ValueError(f"Expected a single type alias, got {ast.unparse(mod)}")
    type_alias = body[0]
    if not isinstance(type_alias, ast.TypeAlias):
        raise ValueError(f"Expected a single type alias, got {ast.unparse(body[0])}")
    dt = kd.Inductive(type_alias.name.id)
    todo = [type_alias.value]
    while todo:
        match todo.pop():
            case ast.BinOp(op=ast.BitOr(), left=left, right=right):
                todo.append(right)
                todo.append(left)
            case ast.Name(id=name):
                dt.declare(name)
            case ast.Call(func=ast.Name(id=name), args=args, keywords=[]):
                dt.declare(
                    name,
                    *[
                        (
                            f"{name}_{n}",
                            _reflect_expr(arg, locals=locals, globals=globals),
                        )
                        for n, arg in enumerate(args)
                    ],
                )
            case ast.Call(func=ast.Name(id=name), args=[], keywords=keywords):
                dt.declare(
                    name,
                    *[
                        (
                            kw.arg,
                            _reflect_expr(kw.value, locals=locals, globals=globals),
                        )
                        for kw in keywords
                    ],
                )
            case _:
                raise ValueError(
                    f"Unexpected subexpression: {ast.unparse(type_alias.value)}"
                )
    return dt.create()
