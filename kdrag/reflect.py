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
