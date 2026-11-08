import kdrag.smt as smt


def test_is_uninterp():
    x = smt.Int("x")
    f = smt.Function("field", smt.IntSort(), smt.IntSort())
    assert smt.is_uninterp(x)
    assert smt.is_uninterp(x.decl())
    assert smt.is_uninterp(f)
    assert smt.is_uninterp(f(x))
    assert not smt.is_uninterp(smt.IntVal(1))
    assert not smt.is_uninterp(x + 1)
    assert not smt.is_uninterp((x + 1).decl())
    assert not smt.is_uninterp(smt.ForAll([x], x == x))


def test_datatype_predicates():
    D = smt.Datatype("SMTPredicateRecord")
    D.declare("unit")
    D.declare("record", ("field", smt.IntSort()))
    D = D.create()
    assert smt.is_constructor(D.unit)
    assert smt.is_constructor(D.unit.decl())
    assert smt.is_constructor(D.record)
    assert smt.is_constructor(D.record(1))
    assert smt.is_accessor(D.field)
    assert smt.is_accessor(D.field(D.unit))
    assert smt.is_recognizer(D.is_record)
    assert smt.is_recognizer(D.is_record(D.unit))
    assert smt.is_recognizer(D.is_record(D.unit).decl())
    assert not smt.is_constructor(D.field)
    assert not smt.is_accessor(D.record)
    assert not smt.is_recognizer(D.record)
    assert not smt.is_uninterp(D.field)
    # The same printed name does not make a user function a datatype accessor.
    f = smt.Function("field", smt.IntSort(), smt.IntSort())
    assert not smt.is_accessor(f)


def test_builtin_sort_predicates():
    assert smt.is_int_sort(smt.IntSort())
    assert smt.is_real_sort(smt.RealSort())
    assert smt.is_bool_sort(smt.BoolSort())
    assert not smt.is_int_sort(smt.RealSort())
    assert not smt.is_real_sort(smt.BoolSort())
    assert not smt.is_bool_sort(smt.IntSort())
    assert not smt.is_int_sort(smt.DeclareSort("Int"))
    assert not smt.is_real_sort(smt.DeclareSort("Real"))
    assert not smt.is_bool_sort(smt.DeclareSort("Bool"))
    assert not smt.is_int_sort(smt.ArraySort(smt.IntSort(), smt.RealSort()))


def test_sort_predicates_in_another_context():
    ctx = smt.Context()
    assert smt.is_int_sort(smt.IntSort(ctx))
    assert smt.is_real_sort(smt.RealSort(ctx))
    assert smt.is_bool_sort(smt.BoolSort(ctx))
