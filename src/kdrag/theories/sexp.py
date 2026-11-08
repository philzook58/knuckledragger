import kdrag as kd
from kdrag import Inductive, NewType, QForAll, axiom, prove  # noqa: F401
import kdrag.smt as smt
from kdrag.smt import (  # noqa: F401
    Bool,
    BoolSort,
    BoolVal,
    Concat,
    Const,
    DatatypeSort,
    Empty,
    Function,
    Int,
    SeqSort,
    StringSort,
    StringVal,
    Unit,
    deserialize,
)
import kdrag.parsers.sexp as sexp_parse


Sexp = NewType("Sexp", StringSort())


def Quote(e: smt.ExprRef) -> tuple[smt.ExprRef, kd.Proof, kd.Proof]:
    """
    Quote an expression as an s-expression.

    >>> x = Int("x")
    >>> sexp, _ ,_ = Quote(x + 1)
    >>> sexp
    Sexp("(declare-fun F (Int) Bool)
    (declare-fun x () Int)
    (assert (F (+ x 1)))
    ")
    """
    sort = e.sort()
    has_interp = Function("has_interp", Sexp, sort, BoolSort())
    interp = Function("interp", Sexp, sort)
    q = Sexp.mk(StringVal(e.serialize()))
    return q, axiom(has_interp(q, e)), axiom(interp(q) == e)


truth = Function("truth", Sexp, BoolSort())
has_interp = Function("has_interp", Sexp, BoolSort(), BoolSort())
interp = Function("interp", Sexp, BoolSort())

q = Const("q", Sexp)
p = Bool("p")
tarski_def = axiom(QForAll([q, p], has_interp(q, p), truth(q), p))


def Truth(pf: kd.Proof) -> tuple[smt.ExprRef, kd.Proof, kd.Proof, kd.Proof]:
    """

    https://en.wikipedia.org/wiki/Tarski%27s_undefinability_theorem

    >>> p = prove(BoolVal(True))
    >>> Truth(p)
    (Sexp("(declare-fun F (Bool) Bool) (assert (F true)) "),
    |= truth(Sexp("(declare-fun F (Bool) Bool) (assert (F true)) ")),
    |= has_interp(Sexp("(declare-fun F (Bool) Bool) (assert (F true)) "),  True),
    |= interp(Sexp("(declare-fun F (Bool) Bool) (assert (F true)) ")) == True)
    """
    assert isinstance(pf, kd.Proof)
    q, hi, i = Quote(pf.thm)
    return q, axiom(truth(q), by=["tarski"]), hi, i


def Unquote(sexp: smt.ExprRef) -> tuple[smt.ExprRef, kd.Proof, kd.Proof]:
    """
    Interpret an s-expression as an expression.

    >>> x = Int("x")
    >>> q, hi1, i1 = Quote(x + 1)
    >>> e, hi2, i2 = Unquote(q)
    >>> e
    x + 1
    >>> assert hi1.thm.eq(hi2.thm) and i1.thm.eq(i2.thm)
    """
    assert sexp.sort() == Sexp
    assert sexp.decl() == Sexp.constructor(0)
    e = deserialize(sexp.arg(0).as_string())
    has_interp = Function("has_interp", Sexp, e.sort(), BoolSort())
    interp = Function("interp", Sexp, e.sort())
    return e, axiom(has_interp(sexp, e)), axiom(interp(sexp) == e)


Sexp1 = Inductive("Sexp1")
SexpS = DatatypeSort("Sexp1")
Sexp1.declare("Atom", ("atom", StringSort()))
Sexp1.declare("List", ("seq", SeqSort(SexpS)))
Sexp1 = Sexp1.create()
Atom = Sexp1.constructor(0)
List = Sexp1.constructor(1)


def of_sexp(sexp: sexp_parse.Sexp) -> smt.ExprRef:
    """
    >>> of_sexp(['a', ['b', 'c']])
    List(Concat(Unit(Atom("a")),
                Unit(List(Concat(Unit(Atom("b")),
                                 Unit(Atom("c")))))))
    """
    if isinstance(sexp, list):
        if len(sexp) == 0:
            return List(Empty(Sexp1))
        elif len(sexp) == 1:
            return List(Unit(of_sexp(sexp[0])))
        else:
            return List(Concat(*[Unit(of_sexp(s)) for s in sexp]))
    elif isinstance(sexp, str):
        return Atom(StringVal(sexp))
    else:
        raise TypeError(f"Unexpected type {sexp}, {type(sexp)}")


def parse(s: str) -> smt.ExprRef:
    """
    Parse a string as an s-expression.

    >>> parse("(a b (c d))")
    List(Unit(List(Concat(Unit(Atom("a")),
                        Concat(Unit(Atom("b")),
                                Unit(List(Concat(Unit(Atom("c")),
                                        Unit(Atom("d"))))))))))
    """
    return of_sexp(sexp_parse.parse(s))
