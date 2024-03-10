from dataclasses import dataclass
from typing import Tuple


@dataclass
class Term:
    def __eq__(self, other):
        return Fn("=", (self, other))

    def __add__(self, other):
        return Fn("+", (self, other))

    def __sub__(self, other):
        return Fn("-", (self, other))

    def __mul__(self, other):
        return Fn("*", (self, other))

    def __truediv__(self, other):
        return Fn("/", (self, other))

    def __lt__(self, other):
        return Fn("<", (self, other))

    def __le__(self, other):
        return Fn("<=", (self, other))

    def __gt__(self, other):
        return Fn(">", (self, other))

    def __ge__(self, other):
        return Fn(">=", (self, other))

    def __ne__(self, other):
        return Fn("!=", (self, other))

    def __neg__(self):
        return Fn("-", (self,))

    def __and__(self, other):
        return Fn("&", (self, other))

    def __or__(self, other):
        return Fn("|", (self, other))

    def __invert__(self):
        return Fn("~", (self,))

    def __lshift__(self, other):
        return Fn("<<", (self, other))

    def __rshift__(self, other):
        return Fn(">>", (self, other))

    def __matmul__(self, other):
        return Fn("@", (self, other))

    def __pow__(self, other):
        return Fn("**", (self, other))

    def __mod__(self, other):
        return Fn("%", (self, other))


# consider hash consing
@dataclass
class Var(Term):
    name: str

    def __init__(self, name):
        assert name[0].isupper()
        self.name = name

    def __repr__(self):
        return self.name


@dataclass
class Fn(Term):
    name: str
    args: Tuple[Term]

    def __repr__(self):
        return f"{self.name}({', '.join(map(repr, self.args))})"


def Vars(names):
    return [Var(name) for name in names.split()]


def Function(name):
    return lambda *args: Fn(name, args)


def Const(name):
    return Fn(name, ())


def Consts(names):
    return [Const(name) for name in names.split()]


def Functions(names):
    return [Function(name) for name in names.split()]


def term_to_sexp(term):
    match term:
        case Var(name):
            return name
        case Fn(name, args):
            return [name, *map(term_to_sexp, args)]
        case _:
            raise TypeError(f"Unknown term type: {type(term)}")


def term_of_sexp(sexp):
    if isinstance(sexp, list):
        return Fn(sexp[0], tuple(term_of_sexp(arg) for arg in sexp[1:]))
    elif isinstance(sexp, str):
        return Var(sexp)


# term_to_z3
# term_of_z3
