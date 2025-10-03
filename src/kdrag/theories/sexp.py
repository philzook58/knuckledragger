import kdrag as kd
import kdrag.smt as smt
import kdrag.parsers.sexp as sexp_parse


Sexp = kd.NewType("Sexp", smt.StringSort())


def Quote(e: smt.ExprRef) -> tuple[smt.ExprRef, kd.Proof, kd.Proof]:
    """
    Quote an expression as an s-expression.

    >>> x = smt.Int("x")
    >>> sexp, _ ,_ = Quote(x + 1)
    >>> sexp
    Sexp("(declare-fun F (Int) Bool)
    (declare-fun x () Int)
    (assert (F (+ x 1)))
    ")
    """
    sort = e.sort()
    has_interp = smt.Function("has_interp", Sexp, sort, smt.BoolSort())
    interp = smt.Function("interp", Sexp, sort)
    q = Sexp.mk(smt.StringVal(e.serialize()))
    return q, kd.axiom(has_interp(q, e)), kd.axiom(interp(q) == e)


truth = smt.Function("truth", Sexp, smt.BoolSort())
has_interp = smt.Function("has_interp", Sexp, smt.BoolSort(), smt.BoolSort())
interp = smt.Function("interp", Sexp, smt.BoolSort())

q = smt.Const("q", Sexp)
p = smt.Bool("p")
tarski_def = kd.axiom(kd.QForAll([q, p], has_interp(q, p), truth(q), p))


def Truth(pf: kd.Proof) -> tuple[smt.ExprRef, kd.Proof, kd.Proof, kd.Proof]:
    """

    https://en.wikipedia.org/wiki/Tarski%27s_undefinability_theorem

    >>> p = kd.prove(smt.BoolVal(True))
    >>> Truth(p)
    (Sexp("(declare-fun F (Bool) Bool) (assert (F true)) "),
    |= truth(Sexp("(declare-fun F (Bool) Bool) (assert (F true)) ")),
    |= has_interp(Sexp("(declare-fun F (Bool) Bool) (assert (F true)) "),  True),
    |= interp(Sexp("(declare-fun F (Bool) Bool) (assert (F true)) ")) == True)
    """
    assert isinstance(pf, kd.Proof)
    q, hi, i = Quote(pf.thm)
    return q, kd.axiom(truth(q), by=["tarski"]), hi, i


def Unquote(sexp: smt.ExprRef) -> tuple[smt.ExprRef, kd.Proof, kd.Proof]:
    """
    Interpret an s-expression as an expression.

    >>> x = smt.Int("x")
    >>> q, hi1, i1 = Quote(x + 1)
    >>> e, hi2, i2 = Unquote(q)
    >>> e
    x + 1
    >>> assert hi1.thm.eq(hi2.thm) and i1.thm.eq(i2.thm)
    """
    assert sexp.sort() == Sexp
    assert sexp.decl() == Sexp.constructor(0)
    e = smt.deserialize(sexp.arg(0).as_string())
    has_interp = smt.Function("has_interp", Sexp, e.sort(), smt.BoolSort())
    interp = smt.Function("interp", Sexp, e.sort())
    return e, kd.axiom(has_interp(sexp, e)), kd.axiom(interp(sexp) == e)


Sexp1 = kd.Inductive("Sexp1")
SexpS = smt.DatatypeSort("Sexp1")
Sexp1.declare("Atom", ("atom", smt.StringSort()))
Sexp1.declare("List", ("seq", smt.SeqSort(SexpS)))
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
            return List(smt.Empty(Sexp1))
        elif len(sexp) == 1:
            return List(smt.Unit(of_sexp(sexp[0])))
        else:
            return List(smt.Concat(*[smt.Unit(of_sexp(s)) for s in sexp]))
    elif isinstance(sexp, str):
        return Atom(smt.StringVal(sexp))
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
