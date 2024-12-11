import kdrag.parsers as parsers
import kdrag.parsers.prolog as prolog
import kdrag.parsers.tptp as tptp
import kdrag.parsers.smtlib as smtlib
import lark
import kdrag.smt as smt


def test_prolog():
    ex1 = """add(z,Y,Y).
    add(s(X),Y,s(Z)) :- add(X,Y,Z).
    ?- add(s(s(z)),s(z),X)."""
    t = prolog.parser.parse(ex1)
    Term = prolog.Term
    add = smt.Function("add", Term, Term, Term, smt.BoolSort())
    s = smt.Function("s", Term, Term)
    z, X, Y, Z = smt.Consts("z X Y Z", Term)
    assert prolog.interp(t)[0].eq(add(z, Y, Y))
    assert prolog.interp(t)[1].eq(
        smt.Implies(smt.And(add(s(X), Y, s(Z)), add(X, Y, Z)), add(s(X), Y, s(Z)))
    )


def test_tptp():
    pass


def test_smtlib():
    ex1 = """
    (assert (= 1 1))
    (check-sat)
    (get-model)
    """
    t = smtlib.parser.parse(ex1)
