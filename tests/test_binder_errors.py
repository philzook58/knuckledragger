import pytest

from kdrag.smt import Exists, ForAll, Int, Lambda, Z3Exception, simplify


@pytest.mark.parametrize("binder", [ForAll, Exists, Lambda])
def test_binder_error_reports_invalid_variables(binder):
    x = Int("binder_x")
    with pytest.raises(Z3Exception) as exc:
        binder([42], x > 0)
    message = str(exc.value)
    assert f"{binder.__name__}:" in message
    assert "variables [42]" in message
    assert "binder_x > 0" in message
    assert isinstance(exc.value.__cause__, AttributeError)


@pytest.mark.parametrize("binder", [ForAll, Exists])
def test_quantifier_error_reports_non_boolean_body(binder):
    x = Int("binder_x")
    with pytest.raises(Z3Exception) as exc:
        binder(x, x)
    assert "variables [binder_x], bodies (binder_x,)" in str(exc.value)
    assert isinstance(exc.value.__cause__, Z3Exception)


def test_lambda_error_reports_non_expression_body():
    x = Int("binder_x")
    with pytest.raises(Z3Exception) as exc:
        Lambda(x, None)
    assert "Lambda:" in str(exc.value)
    assert "body None" in str(exc.value)


def test_binder_wrappers_preserve_valid_construction():
    x = Int("binder_x")
    assert ForAll(x, True).body().eq(ForAll([x], True).body())
    assert Exists(x, x > 0, x < 2).body().eq(Exists([x], x > 0, x < 2).body())
    assert simplify(Lambda(x, x + 1)(2)).as_long() == 3
    assert ForAll(x, x == x, weight=3).weight() == 3
