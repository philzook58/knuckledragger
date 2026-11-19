import pytest

from kdrag import Lemma, define, indrel, prove
from kdrag import kernel
from kdrag.smt import (
    And,
    ArraySort,
    BoolSort,
    Const,
    Exists,
    ForAll,
    Function,
    Int,
    IntSort,
    Ints,
    Lambda,
    Not,
    Select,
)


def test_integer_lt():
    x, y = Ints("indrel_x indrel_y")
    lt = Function("indrel_lt", IntSort(), IntSort(), BoolSort())
    lt = indrel(
        "indrel_lt", [x, y], And(x >= 0, x == 0, y > 0), And(x >= 0, lt(x - 1, y - 1))
    )
    prove(lt(0, 1), by=[lt.case0])
    prove(lt(1, 2), by=[lt.case0, lt.case1])
    invariant = Lambda([x, y], And(x >= 0, x < y))
    prove(ForAll([x, y], lt(x, y), And(x >= 0, x < y)), by=[lt.induct(invariant)])
    # Keep y general while inducting on x so it can decrease in the IH.
    pf = Lemma(ForAll(x, ForAll(y, And(x >= 0, x < y), lt(x, y))))
    a = pf.fix()
    pf.induct(a)
    a = pf.fix()
    pf.intros()
    _b = pf.fix()
    pf.intro()
    pf.auto()
    _b = pf.fix()
    pf.intro()
    pf.auto(by=[lt.case0])
    a = pf.fix()
    pf.intros()
    _b = pf.fix()
    pf.intro()
    pf.auto(by=[lt.case1])
    complete = pf.qed()
    prove(
        ForAll([x, y], lt(x, y) == And(x >= 0, x < y)),
        by=[complete, lt.induct(invariant)],
    )
    pf = Lemma(lt(0, 1))
    pf.unfold(lt)
    pf.auto()
    pf.qed()


def test_empty_and_self_loop():
    x = Int("indrel_empty_x")
    empty = indrel("indrel_empty", x)
    prove(ForAll(x, Not(empty(x))), by=[empty.induct(Lambda(x, x != x))])
    loop = Function("indrel_loop", IntSort(), BoolSort())
    loop = indrel("indrel_loop", x, loop(x))
    prove(ForAll(x, Not(loop(x))), by=[loop.induct(Lambda(x, x != x))])


def test_mixed_sorts_and_existential():
    x, n = Ints("indrel_mix_x indrel_mix_n")
    b = Const("indrel_mix_b", BoolSort())
    rel = Function("indrel_mixed", IntSort(), BoolSort(), BoolSort())
    rel = indrel(
        "indrel_mixed",
        [x, b],
        Exists(n, And(x == n + 1, n >= 0, b)),
        And(x > 1, rel(x - 1, b)),
    )
    prove(rel(1, True), by=[rel.case0])
    prove(rel(2, True), by=[rel.case0, rel.case1])
    prove(Not(rel(1, False)), by=[rel.induct(Lambda([x, b], b))])


def test_quantified_recursion_and_mono_by():
    x, n = Ints("indrel_all_x indrel_all_n")
    rel = Function("indrel_all", IntSort(), BoolSort())
    rel = indrel("indrel_all", x, ForAll(n, rel(n)))
    prove(Not(rel(0)), by=[rel.induct(Lambda(x, x != x))])
    sets = ArraySort(IntSort(), BoolSort())
    helper = Function("indrel_helper", sets, IntSort(), BoolSort())
    A = Const("indrel_helper_A", sets)
    helper = define("indrel_helper", [A, x], Select(A, x))
    law = helper.defn
    rel = Function("indrel_helper_rel", IntSort(), BoolSort())
    body = helper(Lambda(x, rel(x)), x)
    with pytest.raises(ValueError, match="monotonicity"):
        indrel("indrel_helper_rel", x, body)
    assert rel not in kernel.defns
    rel = indrel("indrel_helper_rel", x, body, mono_by=[law])
    prove(Not(rel(0)), by=[rel.induct(Lambda(x, x != x)), law])


def test_rejections():
    x = Const("indrel_bad_x", BoolSort())
    bad = Function("indrel_bad", BoolSort(), BoolSort())
    with pytest.raises(ValueError, match="monotonicity"):
        indrel("indrel_bad", x, Not(bad(Not(x))))
    assert bad not in kernel.defns
    with pytest.raises(ValueError, match="distinct"):
        indrel("indrel_duplicate", [x, x], x)
    with pytest.raises(TypeError, match="Boolean"):
        indrel("indrel_nonbool", x, Int("not_bool"))
    with pytest.raises(ValueError, match="nonempty"):
        indrel("indrel_nullary", [], x)
    f = indrel("indrel_defined", x, x)
    with pytest.raises(ValueError, match="already defined"):
        indrel("indrel_defined", x, x)
    assert f in kernel.defns
