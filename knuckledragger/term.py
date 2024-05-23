from dataclasses import dataclass
from .sort import BoolSort


@dataclass(frozen=True)
class Term:
    def fof(self):
        raise NotImplementedError

    def thf(self):  # default implementation
        return self.fof()

    def __eq__(self, other):
        return Eq(self, other)

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


"""
    def vars(self):
        match self:
            case Var(name):
                return {self}
            case Fn(_, args):
                return set().union(*[arg.vars() for arg in args])
"""


# consider hash consing
@dataclass(frozen=True)
class Var(Term):
    name: str

    # def __init__(self, name):
    #    assert name[0].isupper()
    #    self.name = name

    def __repr__(self):
        return self.name

    def fof(self):
        return self.name


@dataclass(frozen=True)
class Fn(Term):
    name: str
    args: tuple[Term, ...]

    def __repr__(self):
        if len(self.args) == 0:
            return self.name
        return f"{self.name}({', '.join(map(repr, self.args))})"

    def fof(self):
        assert self.name[0].isupper()
        return repr(self)


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
"""
import knuckledragger.term as term
def term_to_tptp(t):
    match t:
        case term.Var(name):
            return name.title()
        case term.Fn(head, args):
            return f"{head}({', '.join([term_to_tptp(x) for x in args])}))"
"""


### Formulas


"""
@dataclass
class Sequent:
    hyps: list[Term]
    conc: Term

    def __repr__(self):
        return f"{self.hyps} |- {self.conc}"

    def tptp_fof(self):
        vs = [hyp.vars() for hyp in self.hyps]
        vs.append(self.conc.vars())
        vs = set().union(*vs)
        f"[{",".join(vs)}] : ( ({" & ".join(self.hyps)}) => {self.conc} )"

    def tptp_cnf(self):
        hyps = [f"~({hyp})" for hyp in self.hyps]
        return f" {" | ".join(hyps)} | {self.conc} )."
"""


@dataclass(frozen=True)
class Formula(Term):
    @property
    def ty(self):
        return BoolSort

    def __eq__(self, other):
        return Iff(self, other)

    def __invert__(self):
        return Not(self)


@dataclass(frozen=True)
class FTrue(Formula):
    def thf(self):
        return "$true"


@dataclass(frozen=True)
class FFalse(Formula):
    def thf(self):
        return "$false"


@dataclass(frozen=True)
class Not(Formula):
    arg: Formula

    def __repr__(self):
        return f"~({self.arg.thf()})"


@dataclass(frozen=True)
class And(Formula):
    x: Formula
    y: Formula

    def thf(self):
        return f"({self.x.thf()} & {self.y.thf()})"


@dataclass(frozen=True)
class Or(Formula):
    x: Formula
    y: Formula

    def thf(self):
        return f"({self.args[0].thf()} | {self.args[1].thf()})"


@dataclass(frozen=True)
class Implies(Formula):
    hyp: Formula
    conc: Formula

    def thf(self):
        return f"({self.hyp.thf()} => {self.conc.thf()})"


@dataclass(frozen=True)
class Iff(Formula):
    lhs: Formula
    rhs: Formula

    def thf(self):
        return f"({self.lhs.thf()} <=> {self.rhs.thf()})"


# def Quantifier(Formula):


@dataclass(frozen=True)
class ForAll(Formula):
    vars: tuple[Var, ...]
    body: Formula

    def __post_init__(self):
        assert all(isinstance(v, Var) for v in self.vars)

    def thf(self):
        return f"! [ {self.var} ] : ({self.body.thf()})"


@dataclass(frozen=True)
class Exists(Formula):
    var: str
    body: Formula

    def thf(self):
        return f"? [ {self.var} ] : ({self.body.thf()})"


"""
@dataclass(frozen=True)
class Atom(Formula):
    pred: str
    args: tuple[Term]
"""


@dataclass(frozen=True)
class Eq(Formula):
    lhs: Term
    rhs: Term

    def thf(self):
        return f"({self.lhs.thf()} = {self.rhs.thf()})"
