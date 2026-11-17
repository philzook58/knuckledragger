from kdrag import QForAll, Theorem, axiom, define, prove
from kdrag.smt import (
    And,
    Const,
    Consts,
    Exists,
    ForAll,
    Function,
    IntSort,
    Lambda,
    RealSort,
)
from kdrag.theories.real import RSet, RSetSeq

x, y, z, M, c = Consts("x y z M c", RealSort())
A, B, C = Consts("A B C", RSet)

has_ub = define(
    "has_ub",
    [A, M],
    QForAll(
        [x],
        A[x],
        x <= M,
    ),
)
is_ub = define("RSet.is_ub", [A], Exists([M], has_ub(A, M)))

sup = Function("RSet.sup", RSet, RealSort())
sup_ax = axiom(
    ForAll(
        [A, M],
        has_ub(A, M),
        And(
            has_ub(A, sup(A)),
            sup(A) <= M,
        ),
    ),
)

sup_least = prove(
    QForAll([A, M], has_ub(A, M), sup(A) <= M),
    by=[sup_ax],
)

sup_ub = prove(
    QForAll([A, M], has_ub(A, M), has_ub(A, sup(A))),
    by=[sup_ax],
)


@Theorem(ForAll([A, M, x], A[x], has_ub(A, M), x <= sup(A)))
def sup_ge(l):
    A, M, x = l.fixes()
    l.intros()
    l.intros()
    l.have(has_ub(A, sup(A)), by=[sup_ub(A, M)])
    l.auto(by=[has_ub.defn])


has_max = define("has_max", [A, x], And(A[x], sup(A) == x))

shift = define(
    "shift",
    [A, c],
    Lambda([x], A[x - c]),
)

sing = define(
    "RSet.sing",
    [c],
    Lambda([x], x == c),
)
sing_elem = prove(
    QForAll([c, x], sing(c)[x] == (x == c)),
    by=[sing.defn],
)


has_lb = define(
    "RSet.has_lb",
    [A, M],
    QForAll(
        [x],
        A[x],
        M <= x,
    ),
)

inf = define("RSet.inf", [A], sup(Lambda([x], has_lb(A, x))))


lb_le_ub = prove(
    ForAll([A, x, y, z], A[x], has_lb(A, y), has_ub(A, z), y <= z),
    by=[has_lb.defn, has_ub.defn],
)


@Theorem(ForAll([A, M], has_lb(A, M), has_lb(A, inf(A))))
def lb_inf(l):
    A, M = l.fixes()
    l.unfold(has_lb)
    l.unfold(inf)
    l.intros()

    x = l.fix()
    l.specialize(0, x)
    l.intros()
    l.have(M <= x, by=[])
    l.apply(sup_least)
    l.unfold(has_ub)
    _y = l.fix()
    l.simp()
    l.unfold(has_lb)
    l.intros()
    l.auto()


An = Const("An", RSetSeq)
n = Const("n", IntSort())

nested = define("nested", [An], ForAll(n, n >= 0, An[n + 1] <= An[n]))
