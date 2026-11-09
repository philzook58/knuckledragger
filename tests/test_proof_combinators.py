import pytest

import kdrag as kd
import kdrag.smt as smt


@pytest.mark.parametrize("prefix", ["w", "witness"])
def test_exists_abstracts_multiple_terms(prefix):
    two, three = smt.IntVal(2), smt.IntVal(3)
    x, y = smt.Ints("exists_x exists_y")
    pf = kd.prove(two + three == 5).exists([two, three], prefix=prefix)
    assert kd.utils.alpha_eq(pf.thm, smt.Exists([x, y], x + y == 5))
    assert all(pf.thm.var_name(i).startswith(prefix + "!") for i in range(2))
    assert pf.thm.var_name(0) != pf.thm.var_name(1)


def test_exists_abstracts_overlapping_terms_simultaneously():
    x, u, v = smt.Ints("exists_x exists_u exists_v")
    pf = kd.prove((x + 1) - x == 1).exists([x + 1, x])
    assert kd.utils.alpha_eq(pf.thm, smt.Exists([u, v], u - v == 1))


def test_exists_preserves_nested_binders():
    x, y, w = smt.Ints("exists_x exists_y exists_w")
    pf = kd.prove(smt.ForAll(y, x + y == y + x)).exists([x])
    expected = smt.Exists(w, smt.ForAll(y, w + y == y + w))
    assert kd.utils.alpha_eq(pf.thm, expected)


def test_obtain_returns_witnesses_and_body_proof():
    x, y = smt.Ints("obtain_x obtain_y")
    pf = kd.prove(smt.Exists([x, y], smt.And(x > 0, y > x)))
    [a, b], body = pf.obtain()
    assert body.thm.eq(smt.And(a > 0, b > a))
    positive, larger = body
    assert positive.thm.eq(a > 0)
    assert larger.thm.eq(b > a)
    [a2, b2], _ = pf.obtain()
    assert not a.eq(a2) and not b.eq(b2)
    # A chosen witness is not an arbitrary variable we may generalize.
    with pytest.raises(AssertionError):
        positive.forall([a])


def test_obtain_preserves_schema_dependencies():
    x = smt.Int("obtain_x")
    a = kd.FreshVar("obtain_parameter", smt.IntSort())
    pf = kd.prove(smt.Exists(x, x > a))
    [w], body = pf.obtain()
    assert w.num_args() == 1 and w.arg(0).eq(a)
    assert body.thm.eq(w > a)


def test_conjunction_indexing_and_unpacking_preserve_grouping():
    x = smt.Int("conjunction_x")
    grouped = smt.And(x + 0 == x, x * 1 == x)
    pf = kd.prove(smt.And(x == x, grouped))
    first, second = pf
    assert first.thm.eq(x == x)
    assert second.thm.eq(grouped)
    assert pf[0].thm.eq(first.thm)
    assert pf[-1].thm.eq(second.thm)
    assert pf[-2].thm.eq(first.thm)
    assert second[1].thm.eq(x * 1 == x)
    # Passing a Proof to by= must still treat it as one proof.
    kd.prove(grouped, by=pf)
    for index in [2, -3]:
        with pytest.raises(IndexError):
            pf[index]
    with pytest.raises(TypeError, match="integers"):
        pf[:1]


def test_convenience_methods_reject_wrong_forms():
    pf = kd.prove(smt.BoolVal(True))
    with pytest.raises(TypeError, match="existential"):
        pf.obtain()
    with pytest.raises(TypeError, match="indexing"):
        pf[0]
    with pytest.raises(TypeError, match="iteration"):
        iter(pf)
    for terms in [[], [3]]:
        with pytest.raises(TypeError, match="SMT terms"):
            pf.exists(terms)
    x = smt.Int("obtain_x")
    with pytest.raises(TypeError, match="iteration"):
        iter(kd.prove(smt.Exists(x, x > 0)))
