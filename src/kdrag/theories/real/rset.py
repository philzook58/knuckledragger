import kdrag as kd
import kdrag.smt as smt
# import kdrag.theories.real as real

RSet = smt.SetSort(smt.RealSort())
x, y, z, M, c = smt.Consts("x y z M c", smt.RealSort())
A, B, C = smt.Consts("A B C", RSet)

has_ub = kd.define(
    "has_ub",
    [A, M],
    kd.QForAll(
        [x],
        A[x],
        x <= M,
    ),
)
is_ub = kd.define("is_ub", [A], smt.Exists([M], has_ub(A, M)))

sup = smt.Function("sup", RSet, smt.RealSort())
sup_ax = kd.axiom(
    smt.ForAll(
        [A, M],
        has_ub(A, M),
        smt.And(
            has_ub(A, sup(A)),
            sup(A) <= M,
        ),
    ),
)

sup_least = kd.prove(
    kd.QForAll([A, M], has_ub(A, M), sup(A) <= M),
    by=[sup_ax],
)

sup_ub = kd.prove(
    kd.QForAll([A, M], has_ub(A, M), has_ub(A, sup(A))),
    by=[sup_ax],
)


@kd.Theorem(smt.ForAll([A, M, x], A[x], has_ub(A, M), x <= sup(A)))
def sup_ge(l):
    A, M, x = l.fixes()
    l.intros()
    l.have(has_ub(A, sup(A)), by=[sup_ub(A, M)])
    l.auto(by=[has_ub.defn])


has_max = kd.define("has_max", [A, x], smt.And(A[x], sup(A) == x))

# Union and intersection theorems

open_int = kd.define("open_int", [x, y], smt.Lambda([z], smt.And(x < z, z < y)))
closed_int = kd.define("closed_int", [x, y], smt.Lambda([z], smt.And(x <= z, z <= y)))

shift = kd.define(
    "shift",
    [A, c],
    smt.Lambda([x], A[x - c]),
)

sing = kd.define(
    "sing",
    [c],
    smt.Lambda([x], x == c),
)
sing_elem = kd.prove(
    kd.QForAll([c, x], sing(c)[x] == (x == c)),
    by=[sing.defn],
)


has_lb = kd.define(
    "has_lb",
    [A, M],
    kd.QForAll(
        [x],
        A[x],
        M <= x,
    ),
)

inf = kd.define("inf", [A], sup(smt.Lambda([x], has_lb(A, x))))


lb_le_ub = kd.prove(
    smt.ForAll([A, x, y, z], A[x], has_lb(A, y), has_ub(A, z), y <= z),
    by=[has_lb.defn, has_ub.defn],
)

"""
@kd.PTheorem(smt.ForAll([A, x, y, z], A[x], has_lb(A, y), has_ub(A, z), y <= z))
def lb_le_ub(l):
    A, x, y, z = l.fixes()
    l.unfold(has_lb)
    l.unfold(has_ub)
    l.intros()
    l.split(at=0)
    l.specialize(1, x)
    l.specialize(2, x)
    l.have(y <= x, by=[])
    l.have(x <= z, by=[])
    l.auto()
"""


@kd.Theorem(smt.ForAll([A, M], has_lb(A, M), has_lb(A, inf(A))))
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

    # l.have(sup_ax(A, M))
    # l.auto(by=[sup_ax])
    # l.simp()


"""
@kd.PTheorem(smt.ForAll([A, M, x], A[x], has_lb(A, M), M <= inf(A)))
def inf_least(l):
    A, M, x = l.fixes()
    # l.unfold(has_lb)
    l.unfold(inf)
    l.intros()
    # l.have(has_ub())
    # l.apply(sup_ge)

    # l.split(at=0)
    # l.specialize(1, x)
    # l.have(M <= x, by=[])
    # l.unfold(has_lb)

    # l.auto()
"""

SetSeq = smt.ArraySort(smt.IntSort(), RSet)
An = smt.Const("An", SetSeq)
n = smt.Const("n", smt.IntSort())
cinter = kd.define("cinter", [An], smt.Lambda([x], kd.QForAll([n], An[n][x])))
cunion = kd.define("cunion", [An], smt.Lambda([x], smt.Exists([n], An[n][x])))

a, b = smt.Consts("a b", smt.ArraySort(smt.IntSort(), smt.RealSort()))
nested = kd.define("nested", [An], kd.QForAll([n], An[n + 1] <= An[n]))
# intseq = kd.define("intseq", [a, b], smt.lambda([n], closed_int(a[n], b[n])))

# nested interval, forall a b, a <= b, nested(intseq(a,b)),  smt.Exists([x], cinter(intseq(a, b))[x])
