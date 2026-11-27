"""The export boundary uses actual theory terms and native SymPy workflows."""

import subprocess
import sys

import pytest

sp = pytest.importorskip("sympy")

import kdrag as kd
import kdrag.smt as smt
from kdrag.solvers.sympy import sympify
from kdrag.theories import real


@pytest.mark.parametrize("name", ["arbitrary_name", "sin", "E", "Symbol", "x!42"])
def test_variables_do_not_use_sympy_namespace(name):
    x = smt.Real(name)
    assert sympify(x + 1) == sp.Symbol(name, real=True) + 1


def test_exact_numbers_and_integer_assumptions():
    i, x = smt.Int("same_name"), smt.Real("same_name")
    si, sx = sympify(i), sympify(x)
    assert si.is_integer is True
    assert sx.is_real is True
    assert si != sx
    assert sympify(i + x) == si + sx
    assert sympify(smt.IntVal(10**80)) == sp.Integer(10**80)
    assert sympify(smt.RatVal(1, 3)) == sp.Rational(1, 3)
    assert sympify(x / 3) == sx / 3
    assert not sympify(smt.RealVal("0.123456789123456789")).has(sp.Float)


@pytest.mark.parametrize(
    "kd_function, sp_function",
    [
        (real.exp, sp.exp),
        (real.ln, sp.log),
        (real.sin, sp.sin),
        (real.cos, sp.cos),
        (real.tan, sp.tan),
        (real.asin, sp.asin),
        (real.acos, sp.acos),
        (real.atan, sp.atan),
        (real.sqrt, sp.sqrt),
        (real.abs, sp.Abs),
        (real.sgn, sp.sign),
        (real.sqr, lambda x: x**2),
    ],
)
def test_real_theory_functions(kd_function, sp_function):
    x = smt.Real("argument")
    assert sympify(kd_function(x)) == sp_function(sympify(x))


def test_real_theory_arithmetic_and_pi():
    x, y = smt.Reals("left right")
    sx, sy = sympify(x), sympify(y)
    assert sympify(real.pi) == sp.pi
    assert sympify(real.add(x, y)) == sx + sy
    assert sympify(real.sub(x, y)) == sx - sy
    assert sympify(real.mul(x, y)) == sx * sy
    assert sympify(real.pow(x, y)) == sx**sy
    assert sympify(real.X)(sx) == sx
    assert sympify(real.const(x))(sy) == sx
    assert sympify(smt.K(real.R, x))(sy) == sx


def test_unary_functions_and_explicit_mappings():
    x = smt.Real("argument")
    f = smt.Function("custom_function", real.R, real.R)
    sx = sympify(x)
    assert sympify(f(x)) == sp.Function("custom_function", real=True)(sx)
    mappings = {"argument": sp.Symbol("t", positive=True), "custom_function": sp.sin}
    before = mappings.copy()
    assert sympify(f(x), locals=mappings) == sp.sin(mappings["argument"])
    assert mappings == before
    # An overloaded declaration must not accidentally become the built-in sine.
    overloaded_sin = smt.Function("sin", real.R, real.R, real.R)
    with pytest.raises(ValueError, match="Cannot export to SymPy"):
        sympify(overloaded_sin(x, x))


def test_relations_and_conditionals():
    x, y = smt.Reals("left right")
    sx, sy = sympify(x), sympify(y)
    pairs = [
        (x == y, sp.Eq(sx, sy)),
        (x != y, sp.Ne(sx, sy)),
        (x < y, sx < sy),
        (x <= y, sx <= sy),
        (x > y, sx > sy),
        (x >= y, sx >= sy),
        (smt.And(x > 0, y > 0), sp.And(sx > 0, sy > 0)),
        (smt.Or(x > 0, y > 0), sp.Or(sx > 0, sy > 0)),
        (smt.Not(x > 0), sp.Not(sx > 0)),
        (smt.Implies(x > 0, y > 0), sp.Implies(sx > 0, sy > 0)),
        (smt.If(x > 0, x, y), sp.Piecewise((sx, sx > 0), (sy, True))),
    ]
    for term, expected in pairs:
        assert sympify(term) == expected
    assert sympify(smt.BoolVal(True)) is sp.true
    assert sympify(smt.BoolVal(False)) is sp.false


def test_lambda_scope_and_argument_order():
    x, y, z = smt.Reals("x y z")
    mappings = {"x": sp.Symbol("free_x"), "z": sp.Symbol("free_z")}
    before = mappings.copy()
    nested = sympify(smt.Lambda([x], smt.Lambda([y], x + y + z)), locals=mappings)
    assert nested(2)(3) == 5 + mappings["z"]
    assert mappings == before
    assert sympify(smt.Lambda([x, y], 2 * x + y))(3, 5) == 11
    lam = sympify(smt.Lambda([x], x + y), locals={"y": sp.Symbol("x", real=True)})
    assert lam(3) == 3 + sp.Symbol("x", real=True)
    assert lam.variables[0].is_real is True
    i = smt.Int("i")
    assert sympify(smt.Lambda([i], i + 1)).variables[0].is_integer is True


def test_calculus_stays_unevaluated_and_scoped():
    x = smt.Real("x")
    sx = sympify(x)
    sine = smt.Lambda([x], real.sin(x))
    derivative = sympify(real.deriv(sine))(sx)
    assert derivative.has(sp.Derivative)
    assert derivative.doit() == sp.cos(sx)
    integral = sympify(real.integrate(sine, 0, x))
    assert isinstance(integral, sp.Integral)
    assert integral.free_symbols == {sx}
    assert integral.doit() == 1 - sp.cos(sx)
    limit = sympify(real.lim(smt.Lambda([x], real.sin(x) / x), 0))
    assert isinstance(limit, sp.Limit)
    assert limit.args[3] == sp.Symbol("+-")
    assert limit.doit() == 1


def test_limit_predicates_export_as_unevaluated_equalities():
    from kdrag.theories.real import seq

    n = smt.Int("n")
    a = smt.Lambda([n], smt.RealVal(1) / n)
    lemma = kd.Lemma(seq.has_lim(a, smt.RealVal(0)))
    before = lemma.top_goal().to_expr()
    result = lemma.sympy()
    assert isinstance(result, sp.Equality)
    assert isinstance(result.lhs, sp.Limit)
    assert result.lhs.args[1].is_integer is True
    assert result.lhs.args[2] is sp.oo
    assert result.rhs == 0
    assert result.doit() is sp.true
    assert lemma.top_goal().to_expr().eq(before)

    unknown = smt.Const("sequence_a", real.RSeq)
    target = smt.Real("target")
    symbolic = sympify(seq.has_lim(unknown, target))
    index = symbolic.lhs.args[1]
    assert symbolic.lhs.args[0] == sp.Function("sequence_a", real=True)(index)
    assert symbolic.rhs == sympify(target)

    x = smt.Real("x")
    at_point = sympify(real.has_lim_at(smt.Lambda([x], real.sin(x) / x), 0, 1))
    assert isinstance(at_point.lhs, sp.Limit)
    assert at_point.lhs.args[2] == 0
    assert at_point.lhs.args[3] == sp.Symbol("+-")
    assert at_point.rhs == 1
    assert at_point.doit() is sp.true


def test_has_sum_exports_an_unevaluated_sum_from_zero():
    from kdrag.theories.real import seq

    n = smt.Int("n")
    a = smt.Lambda([n], smt.RealVal(1) / smt.RealVal(2) ** n)
    lemma = kd.Lemma(seq.has_sum(a, smt.RealVal(2)))
    before = lemma.top_goal().to_expr()
    result = lemma.sympy()
    assert isinstance(result, sp.Equality)
    assert isinstance(result.lhs, sp.Sum)
    index, lower, upper = result.lhs.limits[0]
    assert index.is_integer is True
    assert lower == 0
    assert upper is sp.oo
    assert result.lhs.doit() == 2
    assert result.doit() is sp.true
    assert lemma.top_goal().to_expr().eq(before)

    unknown = smt.Const("sum_sequence", real.RSeq)
    target = smt.Real("n")
    symbolic = sympify(seq.has_sum(unknown, target))
    index = symbolic.lhs.limits[0][0]
    assert symbolic.lhs.function == sp.Function("sum_sequence", real=True)(index)
    assert symbolic.free_symbols == {sympify(target)}


def test_native_integrate_and_dsolve():
    x = smt.Real("x")
    sx = sympify(x)
    assert sp.integrate(sympify(x * real.exp(x)), sx) == (sx - 1) * sp.exp(sx)
    y = smt.Const("y", real.RFun)
    sy = sympify(y[x])
    first = sympify(real.deriv(y)[x])
    second = sympify(real.deriv(real.deriv(y))[x])
    assert first == sp.Derivative(sy, sx)
    assert second == sp.Derivative(sy, (sx, 2))
    solution = sp.dsolve(sympify(real.deriv(y)[x] == y[x]), sy, ics={sy.subs(sx, 0): 1})
    assert solution == sp.Eq(sy, sp.exp(sx))


def test_proof_state_sympy_export():
    x = smt.Real("export_x")
    sx = sympify(x)
    lemma = kd.Lemma(smt.ForAll([x], x + 1 == 1 + x))
    fixed = lemma.fix()
    before = lemma.top_goal().to_expr()
    lemmas = lemma.lemmas.copy()
    assert lemma.sympy() == sp.Eq(
        lemma.sympy(fixed) + 1, 1 + lemma.sympy(fixed), evaluate=False
    )
    assert isinstance(lemma.sympy(), sp.Equality)
    assert sp.integrate(lemma.sympy(x**2), lemma.sympy(x)) == sx**3 / 3
    assert lemma.top_goal().to_expr().eq(before)
    assert lemma.lemmas == lemmas
    # Explicit exports are useful even when no goals remain.
    lemma.auto()
    assert lemma.sympy(x) == sx


def test_inspection_helpers_preserve_proof_state():
    x, y = smt.Reals("helper_x helper_y")
    sx, sy = sympify(x), sympify(y)
    cases = [
        (kd.Lemma((x + 1) ** 2 == x**2 + 2 * x + 1), lambda l: l.symp(), sp.true),
        (kd.Lemma(smt.Exists([x], x + y**2 == 1)), lambda l: l.esolve(), None),
        (
            kd.Lemma(smt.Implies(x + y == 10, x == 10 - y)),
            lambda l: l.solve(x),
            {sx: 10 - sy},
        ),
    ]
    cases[2][0].intros()
    for lemma, inspect, expected in cases:
        before = lemma.top_goal().to_expr()
        lemmas = lemma.lemmas.copy()
        result = inspect(lemma)
        if expected is None:
            assert list(result.values()) == [1 - sy**2]
        else:
            assert result == expected
        assert lemma.top_goal().to_expr().eq(before)
        assert lemma.lemmas == lemmas


@pytest.mark.parametrize(
    "term",
    [
        smt.ForAll([smt.Real("x")], smt.Real("x") > 0),
        smt.BitVec("bits", 8),
        smt.Int("n") / 2,
    ],
)
def test_unsupported_constructs_have_specific_errors(term):
    with pytest.raises(ValueError, match="Cannot export to SymPy:.*sort"):
        sympify(term)


def test_normal_import_does_not_load_sympy():
    subprocess.run(
        [
            sys.executable,
            "-B",
            "-c",
            "import sys; import kdrag; import kdrag.theories.real; "
            "assert 'sympy' not in sys.modules; "
            "assert 'kdrag.solvers.sympy' not in sys.modules",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
