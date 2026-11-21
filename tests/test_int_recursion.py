import pytest

from kdrag import kernel, prove
from kdrag.smt import (
    ArraySort,
    BoolSort,
    Empty,
    ForAll,
    FreshFunction,
    If,
    Implies,
    Int,
    IntSort,
    IntVal,
    Lambda,
    Real,
    SeqSort,
)
from kdrag.termination import check_int_recursion, define_rec


def fresh():
    return FreshFunction(IntSort(), IntSort()), Int("rec_n")


def test_factorial_and_fibonacci():
    f, n = fresh()
    assert define_rec(f, n, If(n <= 0, 1, n * f(n - 1))) == f
    prove(f(4) == 24, by=[f.defn(i) for i in range(5)])
    assert f.defn.reason[0] == "integer_recursion"
    f, n = fresh()
    body = If(n <= 1, 1, f(n - 1) + f(n - 2))
    assert len(check_int_recursion(f, n, body)) == 2
    define_rec(f, n, body)
    prove(f(5) == 8, by=[f.defn(i) for i in range(6)])


def test_upward_recursion_on_negative_integers():
    f, n = fresh()
    define_rec(f, n, If(n >= 0, 0, 1 + f(n + 1)))
    prove(f(-2) == 2, by=[f.defn(i) for i in [-2, -1, 0]])


@pytest.mark.parametrize(
    "body",
    [
        lambda f, n: f(n),
        lambda f, n: f(n) + 1,
        lambda f, n: f(n - 1),
        lambda f, n: If(n <= 0, 0, f(n + 1)),
        lambda f, n: If(n >= 0, 1, n * f(n - 1)),
    ],
)
def test_failure_leaves_no_definition_or_reservation(body):
    f, n = fresh()
    with pytest.raises(ValueError, match="decrease obligation"):
        define_rec(f, n, body(f, n))
    assert f not in kernel.defns
    # A successful retry also establishes that rejection did not reserve the name.
    define_rec(f, n, If(n <= 0, 0, f(n - 1)))


@pytest.mark.parametrize(
    "body",
    [
        lambda f, n: If(f(n) > 0, 0, f(n - 1)),
        lambda f, n: If(n <= 0, 0, f(f(n - 1))),
        lambda f, n: If(ForAll([Int("bound")], Int("bound") >= n), 0, f(n - 1)),
    ],
)
def test_unsupported_syntax(body):
    f, n = fresh()
    with pytest.raises(ValueError):
        define_rec(f, n, body(f, n))
    assert f not in kernel.defns


def test_signature_and_redefinition():
    f, n = fresh()
    with pytest.raises(TypeError):
        define_rec(f, n, Real("real_body"))
    define_rec(f, n, n + 1)
    with pytest.raises(ValueError, match="already defined"):
        define_rec(f, n, n + 1)
    with pytest.raises(TypeError, match="arguments"):
        define_rec((-n).decl(), n, n)
    binary = FreshFunction(IntSort(), IntSort(), IntSort())
    with pytest.raises(TypeError, match="arguments"):
        define_rec(binary, n, n)


def test_guarded_branch_context_and_hidden_dependency():
    f, n = fresh()
    define_rec(f, n, If(n > 10, If(n > 0, f(n - 1), f(n)), 0))
    f, n = fresh()
    kernel.define("recursion_wrapper_test", [n], f(n))
    with pytest.raises(ValueError, match="registered definition"):
        define_rec(f, n, If(n <= 0, 0, f(n - 1)))


def test_boolean_codomain():
    n = Int("rec_bool_n")
    even = FreshFunction(IntSort(), BoolSort())
    define_rec(even, n, If(n <= 0, True, ~even(n - 1)))
    prove(even(4), by=[even.defn(i) for i in range(5)])
    prove(~even(3), by=[even.defn(i) for i in range(4)])


def test_sequence_codomain():
    n = Int("rec_seq_n")
    sort = SeqSort(IntSort())
    countdown = FreshFunction(IntSort(), sort)
    define_rec(countdown, n, If(n <= 0, Empty(sort), [n] + countdown(n - 1)))
    prove(
        countdown(2) == [2, 1] + Empty(sort), by=[countdown.defn(i) for i in range(3)]
    )


def test_defined_helpers_and_constants():
    f, n = fresh()
    g = FreshFunction(IntSort(), IntSort())
    kernel.define(g.name(), [n], n + 1)
    initial = kernel.define("rec_initial", [], IntVal(7))
    define_rec(f, n, If(n <= 0, initial, g(f(n - 1))))
    prove(f(2) == g(g(initial)), by=[f.defn(i) for i in range(3)])


def test_previously_defined_helper():
    f, n = fresh()
    g = FreshFunction(IntSort(), IntSort())
    kernel.define(g.name(), [n], n + 1)
    define_rec(f, n, If(n <= 0, 0, g(f(n - 1))))
    prove(f(2) == 2, by=[f.defn(i) for i in range(3)] + [g.defn])


def test_helper_in_decreasing_argument_with_explicit_guard():
    f, n = fresh()
    g = FreshFunction(IntSort(), IntSort())
    kernel.define(g.name(), [n], n - 1)
    define_rec(f, n, If((n > 0) & (g(n) >= 0) & (g(n) < n), f(g(n)), 0))


def test_helpers_do_not_hide_recursive_calls():
    f, n = fresh()
    g = FreshFunction(IntSort(), IntSort())
    kernel.define(g.name(), [n], n)
    for body in [g(f(n)), If(n > 0, f(g(n)), 0)]:
        with pytest.raises(ValueError, match="decrease obligation"):
            define_rec(f, n, body)
        assert f not in kernel.defns
    with pytest.raises(ValueError, match="nested recursive"):
        define_rec(f, n, If(n <= 0, 0, f(g(f(n - 1)))))


def test_changing_parameters():
    n, a, b = Int("param_n"), Int("param_a"), Int("param_b")
    Z = IntSort()
    f = FreshFunction(Z, Z, Z, Z)
    define_rec(f, [n, a, b], If(n <= 0, a, f(n - 1, b, a + b)))
    prove(f(2, 1, 1) == 2, by=[f.defn(2, 1, 1), f.defn(1, 1, 2), f.defn(0, 2, 3)])
    bad = FreshFunction(Z, Z, Z)
    with pytest.raises(ValueError, match="decrease obligation"):
        define_rec(bad, [n, a], If(n <= 0, 0, bad(n, a - 1)))
    with pytest.raises(TypeError, match="distinct"):
        define_rec(bad, [n, n], n)


def test_lambda_variables_are_quantified_and_do_not_shadow_rank():
    Z = IntSort()
    n, x = Int("lambda_rank"), Int("lambda_arg")
    T = ArraySort(Z, Z)
    f = FreshFunction(Z, T)
    certificates = check_int_recursion(
        f, n, If(n <= 0, Lambda([x], x), Lambda([x], f(n - 1)[x] + 1))
    )
    assert certificates[0].thm.num_vars() == 2
    define_rec(f, n, If(n <= 0, Lambda([x], x), Lambda([x], f(n - 1)[x] + 1)))
    prove(f(1)[7] == 8, by=[f.defn(0), f.defn(1)])
    for bound in [x, n]:
        bad = FreshFunction(Z, T)
        with pytest.raises(ValueError, match="decrease obligation"):
            define_rec(
                bad,
                n,
                If(n <= 0, Lambda([x], x), Lambda([bound], bad(bound - 1)[bound])),
            )


def test_nested_recursion_in_parameter_is_rejected():
    Z = IntSort()
    n, a = Int("nested_rank"), Int("nested_param")
    f = FreshFunction(Z, Z, Z)
    with pytest.raises(ValueError, match="nested recursive"):
        define_rec(f, [n, a], If(n <= 0, a, f(n - 1, f(n - 2, a))))


def test_ackermann_example():
    import runpy

    example = runpy.run_path("examples/recursion/ackermann.py")
    assert example["A"].defn.reason[0] == "integer_recursion"
    assert len(example["row"].defn.reason[1]) == 1
    assert len(example["A"].defn.reason[1]) == 1


def test_gassed_sequence_reverse():
    import runpy

    example = runpy.run_path("examples/recursion/reverse.py")
    rev = example["rev"]
    aux = example["rev_aux"]
    S = example["S"]
    # The public equation is derived; the gas recursion alone uses the new rule.
    assert aux.defn.reason[0] == "integer_recursion"
    prove(rev(Empty(S)) == Empty(S), by=[example["rev_eq"]])


def test_undefined_helpers_are_rejected_even_in_guards():
    f, n = fresh()
    g = FreshFunction(IntSort(), IntSort())
    # A declaration by itself is not a definition.
    kernel.declare(g.name(), IntSort(), IntSort())
    for body in [If(n <= 0, 0, g(f(n - 1))), If(g(n) > 0, 0, n)]:
        with pytest.raises(ValueError, match="must be defined"):
            define_rec(f, n, body)
        assert f not in kernel.defns
    kernel.define(g.name(), [n], n + 1)
    define_rec(f, n, If(n <= 0, 0, g(f(n - 1))))


def test_undefined_constants_are_rejected_but_formal_parameters_are_allowed():
    f, n = fresh()
    external = Int("rec_external_constant")
    with pytest.raises(ValueError, match="must be defined"):
        define_rec(f, n, If(n <= 0, external, f(n - 1)))
    assert f not in kernel.defns
    parameterized = FreshFunction(IntSort(), IntSort(), IntSort())
    define_rec(
        parameterized,
        [n, external],
        If(n <= 0, external, parameterized(n - 1, external)),
    )
    kernel.define(external.decl().name(), [], IntVal(3))
    define_rec(f, n, If(n <= 0, external, f(n - 1)))


def test_implication_guards_consequent():
    n = Int("implies_n")
    f = FreshFunction(IntSort(), BoolSort())
    define_rec(f, n, Implies(n > 0, ~f(n - 1)))
    prove(~f(3), by=[f.defn(i) for i in range(4)])


def test_implication_combines_with_enclosing_and_nested_guards():
    n = Int("nested_implies_n")
    f = FreshFunction(IntSort(), BoolSort())
    define_rec(f, n, If(n >= 0, Implies(n > 1, f(n - 2)), Implies(n < 0, f(n + 1))))
    impossible = FreshFunction(IntSort(), BoolSort())
    define_rec(impossible, n, Implies(n > 0, Implies(n <= 0, impossible(n))))
    prove(impossible(n), by=[impossible.defn(n)])


def test_implication_does_not_allow_recursive_conditions_or_increasing_calls():
    n = Int("bad_implies_n")
    f = FreshFunction(IntSort(), BoolSort())
    with pytest.raises(ValueError, match="Recursive conditions"):
        define_rec(f, n, Implies(f(n - 1), True))
    with pytest.raises(ValueError, match="decrease obligation"):
        define_rec(f, n, Implies(n > 0, f(n + 1)))
    assert f not in kernel.defns
