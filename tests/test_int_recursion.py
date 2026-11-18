import pytest

from kdrag import kernel, prove
from kdrag.smt import (
    BoolSort,
    Empty,
    ForAll,
    FreshFunction,
    If,
    Int,
    IntSort,
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
    with pytest.raises(TypeError, match="unary"):
        define_rec((-n).decl(), n, n)
    binary = FreshFunction(IntSort(), IntSort(), IntSort())
    with pytest.raises(TypeError, match="unary"):
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


def test_helpers_and_free_constants():
    f, n = fresh()
    g = FreshFunction(IntSort(), IntSort())
    initial = Int("rec_initial")
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
    define_rec(f, n, If((n > 0) & (g(n) >= 0) & (g(n) < n), f(g(n)), 0))


def test_helpers_do_not_hide_recursive_calls():
    f, n = fresh()
    g = FreshFunction(IntSort(), IntSort())
    for body in [g(f(n)), If(n > 0, f(g(n)), 0)]:
        with pytest.raises(ValueError, match="decrease obligation"):
            define_rec(f, n, body)
        assert f not in kernel.defns
    with pytest.raises(ValueError, match="nested recursive"):
        define_rec(f, n, If(n <= 0, 0, f(g(f(n - 1)))))
