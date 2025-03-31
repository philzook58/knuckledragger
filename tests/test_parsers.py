import kdrag.parsers as parsers
import kdrag.solvers.prolog as prolog
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
    assert prolog.interp(t)[0][0].eq(smt.ForAll([Y], add(z, Y, Y)))
    assert prolog.interp(t)[0][1].eq(smt.ForAll([Y,Z,X],
        smt.Implies( smt.And(add(X, Y, Z)), add(s(X), Y, s(Z)))))


def test_tptp():
    pass


def test_smtlib():
    ex1 = """
    (assert (= 1 1))
    (check-sat)
    (get-model)
    """
    t = smtlib.parser.parse(ex1)
