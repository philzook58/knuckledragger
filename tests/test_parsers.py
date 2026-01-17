import kdrag.parsers as parsers
import kdrag.solvers.prolog as prolog
import kdrag.parsers.tptp as tptp
import kdrag.parsers.smtlib as smtlib
import kdrag.parsers.microlean as microlean
import kdrag.theories.real.seq as seq
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
    print(prolog.interp(t)[0][1])
    # ordering of [X,Y,Z] is not stable in quantifier.
    #assert prolog.interp(t)[0][1].eq(smt.ForAll([X,Y,Z],
    #    smt.Implies( smt.And(add(X, Y, Z)), add(s(X), Y, s(Z)))))


def test_tptp():
    pass


def test_smtlib():
    ex1 = """
    (assert (= 1 1))
    (check-sat)
    (get-model)
    """
    t = smtlib.parser.parse(ex1)


def test_microlean_did_you_mean():
    ex1 = "has_lim (fun (n : Int) => n) 0"
    try:
        microlean.parse(ex1, {"seq": seq})
    except NameError as exc:
        assert "seq.has_lim" in str(exc)
    else:
        raise AssertionError("Expected NameError with suggestion")


def test_microlean_decimal_is_real():
    t = microlean.parse("1.0", {})
    assert t.eq(smt.RealVal("1.0"))
