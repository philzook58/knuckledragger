import pytest

import kdrag.smt as smt


def test_operator_predicates():
    D = smt.Datatype("SMTPredicateRecord")
    D.declare("unit")
    D.declare("record", ("field", smt.IntSort()))
    D = D.create()
    x = smt.Int("x")
    # An uninterpreted function may share an accessor's printed name.
    f = smt.Function("field", smt.IntSort(), smt.IntSort())
    tester = D.is_record(D.unit)
    cases = [
        (x, "uninterp"),
        (x.decl(), "uninterp"),
        (f, "uninterp"),
        (f(x), "uninterp"),
        (D.unit, "constructor"),
        (D.unit.decl(), "constructor"),
        (D.record, "constructor"),
        (D.record(x), "constructor"),
        (D.field, "accessor"),
        (D.field(D.unit), "accessor"),
        (D.is_record, "recognizer"),
        (tester, "recognizer"),
        (tester.decl(), "recognizer"),
        (smt.IntVal(1), None),
        (smt.BoolVal(True), None),
        (x + 1, None),
        ((x + 1).decl(), None),
        (smt.ForAll([x], x == x), None),
        (smt.Lambda([x], x), None),
    ]
    predicates = {
        "uninterp": smt.is_uninterp,
        "constructor": smt.is_constructor,
        "accessor": smt.is_accessor,
        "recognizer": smt.is_recognizer,
    }
    for term, expected in cases:
        for name, predicate in predicates.items():
            assert predicate(term) is (name == expected), (name, term)


@pytest.mark.parametrize("fresh_context", [False, True])
def test_sort_predicates(fresh_context):
    ctx = smt.Context() if fresh_context else None
    predicates = [smt.is_int_sort, smt.is_real_sort, smt.is_bool_sort]
    sorts = [smt.IntSort(ctx), smt.RealSort(ctx), smt.BoolSort(ctx)]
    for index, sort in enumerate(sorts):
        assert [predicate(sort) for predicate in predicates] == [
            index == i for i in range(3)
        ]
    for name in ["Int", "Real", "Bool"]:
        sort = smt.DeclareSort(name)
        assert not any(predicate(sort) for predicate in predicates)
    array = smt.ArraySort(sorts[0], sorts[1])
    assert not any(predicate(array) for predicate in predicates)
