from kdrag import (
    Lemma,
    define_least,
    prove,
    relation_operator,
    least_induct,
    least_unfold,
)
from kdrag.smt import (
    And,
    ArraySort,
    BoolSort,
    BoolVal,
    Const,
    Exists,
    ForAll,
    Function,
    Int,
    IntSort,
    Ints,
    IntVal,
    Lambda,
    Not,
    Or,
    Implies,
)
from kdrag import kernel, smt


def test_unary_operator_and_self_loop():
    x = Int("operator_x")
    rel = Function("operator_loop", IntSort(), BoolSort())
    F = relation_operator(rel, x, rel(x))
    relation = ArraySort(IntSort(), BoolSort())
    assert F.sort() == ArraySort(relation, relation)
    R = Const("operator_R", relation)
    assert F(R)(x).eq(Or(R(x)))
    rel = define_least(rel, x, rel(x))
    pf = Lemma(Implies(rel(x), False))
    member = pf.intro()
    pf.unfold(rel, at=member)
    pf.specialize(pf.top_goal().ctx[-1], Lambda(x, BoolVal(False)))
    pf.auto()
    pf.qed()


def test_multi_argument_operator_and_binders():
    x, n = Ints("operator_mix_x operator_mix_n")
    b = Const("operator_mix_b", BoolSort())
    rel = Function("operator_mix", IntSort(), BoolSort(), BoolSort())
    body = Exists(n, And(n >= 0, rel(x - n, b)))
    F = relation_operator(rel, [x, b], body)
    R = Const("operator_mix_R", ArraySort(IntSort(), BoolSort(), BoolSort()))
    assert F(R)(x, b).eq(Or(Exists(n, And(n >= 0, R(x - n, b)))))
    assert not kernel.decl_occurs(rel, F)
    # Applications inline both lambdas; no Select(Lambda(...), ...) is needed.
    assert F(R).is_lambda()
    assert F(R)(x, b).arg(0).is_exists()


def test_empty_and_nonmonotone_intersections():
    x = Const("intersection_x", BoolSort())
    for name, clauses in [("empty_intersection", ()), ("negative_intersection", None)]:
        rel = Function(name, BoolSort(), BoolSort())
        if clauses is None:
            clauses = (Not(rel(Not(x))),)
        rel = define_least(rel, x, *clauses)
        assert not kernel.decl_occurs(rel, kernel.defns[rel].body)
        assert not hasattr(rel, "induct")
        # Either singleton is closed, hence the intersection contains neither point.
        for point, candidate in [(False, Lambda(x, x)), (True, Lambda(x, Not(x)))]:
            pf = Lemma(Implies(rel(point), False))
            member = pf.intro()
            pf.unfold(rel, at=member)
            pf.specialize(pf.top_goal().ctx[-1], candidate)
            pf.auto()
            pf.qed()


def test_integer_lt_and_manual_leastness():
    x, y = Ints("intersection_lt_x intersection_lt_y")
    rel = Function("intersection_lt", IntSort(), IntSort(), BoolSort())
    clauses = (And(x >= 0, x == 0, y > 0), And(x >= 0, rel(x - 1, y - 1)))
    F = relation_operator(rel, [x, y], *clauses)
    rel = define_least(rel, [x, y], *clauses)
    R = Const("intersection_lt_R", F.sort().domain())
    pf = Lemma(
        ForAll(
            R, ForAll([x, y], F(R)(x, y), R(x, y)), ForAll([x, y], rel(x, y), R(x, y))
        )
    )
    candidate = pf.fix()
    pf.intro()
    pf.fixes()
    member = pf.intro()
    pf.unfold(rel, at=member)
    pf.specialize(pf.top_goal().ctx[-1], candidate)
    pf.auto()
    least = pf.qed()
    prove(
        ForAll([x, y], rel(x, y), And(x >= 0, x < y)),
        by=[least(Lambda([x, y], And(x >= 0, x < y)))],
    )
    for a, b in [(0, 1), (1, 2)]:
        pf = Lemma(rel(a, b))
        pf.unfold(rel)
        pf.fix()
        closed = pf.intro()
        pf.specialize(closed, IntVal(0), IntVal(b - a), keep=True)
        if a:
            pf.specialize(closed, IntVal(a), IntVal(b), keep=True)
        pf.auto()
        pf.qed()


def test_generated_induction_and_unfolding():
    x, n = Ints("generated_x generated_n")
    b = Const("generated_b", BoolSort())
    f = Function("generated_relation", IntSort(), BoolSort(), BoolSort())
    clauses = (Exists(n, And(x == n + 1, n >= 0, b)), And(x > 1, f(x - 1, b)))
    F = relation_operator(f, [x, b], *clauses)
    f = define_least(f, [x, b], *clauses)
    original = f.defn
    induction = least_induct(F)
    invariant = induction(Lambda([x, b], b))
    closed = prove(invariant.thm.arg(0))
    inclusion = invariant(closed)
    assert inclusion.thm.is_forall()
    conditional = least_unfold(F)
    mono = prove(conditional.thm.arg(0))
    equation = conditional(mono)
    assert equation.thm.is_forall()
    assert smt.is_eq(equation.thm.body())
    assert f.defn is original
    assert not hasattr(f, "induct")


def test_conditional_unfolding_for_negative_operator():
    x = Const("generated_negative_x", BoolSort())
    f = Function("generated_negative", BoolSort(), BoolSort())
    F = relation_operator(f, x, Not(f(Not(x))))
    rule = least_unfold(F)
    # The generator does not assume monotonicity or assert an unconditional equation.
    assert smt.is_implies(rule.thm)
    prove(Not(rule.thm.arg(0)))


def test_abstract_operator():
    relation = ArraySort(IntSort(), BoolSort())
    F = Const("abstract_relation_operator", ArraySort(relation, relation))
    assert isinstance(least_induct(F), kernel.Proof)
    assert smt.is_implies(least_unfold(F).thm)
