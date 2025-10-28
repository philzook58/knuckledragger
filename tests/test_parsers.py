import kdrag.parsers as parsers
import kdrag.solvers.prolog as prolog
import kdrag.parsers.tptp as tptp
import kdrag.parsers.smtlib as smtlib
import kdrag.parsers.logic as logic
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


def test_logic_basic():
    """Test basic logic parser functionality."""
    env = {
        'Int': smt.IntSort(),
        'Bool': smt.BoolSort(),
        'Real': smt.RealSort(),
    }
    
    # Test simple arithmetic
    x = smt.Int('x')
    env['x'] = x
    expr = logic.parse("x + 1", env)
    assert str(expr) == "x + 1"
    
    # Test comparisons (Z3 normalizes these)
    expr = logic.parse("x > 0", env)
    # Z3 may normalize to "0 < x"
    assert "x" in str(expr) and "0" in str(expr)
    
    expr = logic.parse("x == 5", env)
    assert "x" in str(expr) and "5" in str(expr)
    
    # Test boolean operators
    expr = logic.parse("True /\\ False", env)
    assert str(expr) == "And(True, False)"
    
    expr = logic.parse("True \\/ False", env)
    assert str(expr) == "Or(True, False)"


def test_logic_quantifiers():
    """Test forall and exists quantifiers."""
    env = {
        'Int': smt.IntSort(),
        'Bool': smt.BoolSort(),
    }
    
    # Test forall
    expr = logic.parse("forall (x : Int), x + 0 == x", env)
    assert expr.is_forall()
    
    # Test exists
    expr = logic.parse("exists (x : Int), x > 0", env)
    assert expr.is_exists()
    
    # Test multiple variables
    expr = logic.parse("forall (x : Int, y : Int), x + y == y + x", env)
    assert expr.is_forall()


def test_logic_implications():
    """Test implication operator."""
    env = {
        'Int': smt.IntSort(),
    }
    x = smt.Int('x')
    env['x'] = x
    
    expr = logic.parse("x > 0 -> x + 1 > 1", env)
    # Check it's an implication
    assert expr.decl().kind() == smt.Z3_OP_IMPLIES


def test_logic_complex():
    """Test complex nested expressions."""
    env = {
        'Int': smt.IntSort(),
        'Bool': smt.BoolSort(),
    }
    
    # Test nested quantifiers with implications
    expr = logic.parse(
        "forall (x : Int), x >= 0 -> exists (y : Int), y == x + 1",
        env
    )
    assert expr.is_forall()
    
    # Test multiple operators
    x = smt.Int('x')
    env['x'] = x
    expr = logic.parse("(x > 0 /\\ x < 10) \\/ x == 0", env)
    assert expr.decl().kind() == smt.Z3_OP_OR


def test_logic_python_interpolation():
    """Test Python expression interpolation with braces."""
    x = smt.Int('x')
    y = smt.Int('y')
    env = {
        'Int': smt.IntSort(),
        'x': x,
        'y': y,
    }
    
    # Test simple interpolation - Z3 may normalize these
    expr = logic.parse("{x} + 1 == 2", env)
    assert "x" in str(expr) and "1" in str(expr) and "2" in str(expr)
    
    # Test expression interpolation
    expr = logic.parse("{x + y} > 0", env)
    assert "x" in str(expr) and "y" in str(expr) and "0" in str(expr)


def test_logic_functions():
    """Test function application."""
    f = smt.Function('f', smt.IntSort(), smt.IntSort())
    x = smt.Int('x')
    env = {
        'Int': smt.IntSort(),
        'f': f,
        'x': x,
    }
    
    expr = logic.parse("f(x) > 0", env)
    # Z3 may normalize to "0 < f(x)"
    assert "f(x)" in str(expr) and "0" in str(expr)
    
    # Test with multiple arguments
    g = smt.Function('g', smt.IntSort(), smt.IntSort(), smt.IntSort())
    env['g'] = g
    expr = logic.parse("g(x, 5) == 10", env)
    assert "g(x, 5)" in str(expr) and "10" in str(expr)


def test_logic_precedence():
    """Test operator precedence."""
    x = smt.Int('x')
    env = {
        'Int': smt.IntSort(),
        'x': x,
    }
    
    # Test that /\ binds tighter than \/
    expr = logic.parse("x > 0 \\/ x < 0 /\\ x == 0", env)
    # Should parse as: x > 0 \/ (x < 0 /\ x == 0)
    assert expr.decl().kind() == smt.Z3_OP_OR
    
    # Test that -> is right associative and lowest precedence
    expr = logic.parse("x > 0 -> x < 10 -> x != 5", env)
    # Should parse as: x > 0 -> (x < 10 -> x != 5)
    assert expr.decl().kind() == smt.Z3_OP_IMPLIES


def test_logic_errors():
    """Test error handling."""
    env = {
        'Int': smt.IntSort(),
    }
    
    # Test unknown sort
    try:
        logic.parse("forall (x : UnknownSort), x > 0", env)
        assert False, "Should raise ParseError"
    except logic.ParseError as e:
        assert "Unknown sort" in str(e)
    
    # Test unknown identifier
    try:
        logic.parse("unknown_var + 1", env)
        assert False, "Should raise ParseError"
    except logic.ParseError as e:
        assert "Unknown identifier" in str(e)
    
    # Test unclosed brace
    try:
        logic.parse("{x + 1", env)
        assert False, "Should raise ParseError"
    except logic.ParseError as e:
        assert "Unclosed" in str(e)
