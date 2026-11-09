import kdrag as kd
from kdrag import QForAll, Theorem, axiom, define, prove
from kdrag.smt import (
    And,
    ArraySort,
    BoolSort,
    Const,
    Consts,
    DeclareSort,
    ForAll,
    Function,
    Implies,
    Lambda,
    SetSort,
)

# Declare an abstract complete lattice
L = DeclareSort("L")
SetL = SetSort(L)

x, y, z = Consts("x y z", L)
A, B = Consts("A B", SetL)

le = Function("le", L, L, BoolSort())
kd.notation.le.register(L, le)

le_refl = axiom(ForAll([x], x <= x))
le_trans = axiom(ForAll([x, y, z], Implies(And(x <= y, y <= z), x <= z)))
le_antisym = axiom(ForAll([x, y], Implies(And(x <= y, y <= x), x == y)))

is_ub = define("is_ub", [A, y], QForAll([x], A[x], x <= y))
is_lb = define("is_lb", [A, y], QForAll([x], A[x], y <= x))

sup = Function("sup", SetL, L)
inf = Function("inf", SetL, L)

sup_is_ub = axiom(ForAll([A], is_ub(A, sup(A))))
sup_least = axiom(ForAll([A, y], Implies(is_ub(A, y), sup(A) <= y)))

inf_is_lb = axiom(ForAll([A], is_lb(A, inf(A))))
inf_greatest = axiom(ForAll([A, y], Implies(is_lb(A, y), y <= inf(A))))

# Monotone functions on L (represented as arrays L -> L)
FSort = ArraySort(L, L)
f = Const("f", FSort)

monotone = define("monotone", [f], ForAll([x, y], Implies(x <= y, f[x] <= f[y])))

prefixed = define("prefixed", [f], Lambda([x], f[x] <= x))
postfixed = define("postfixed", [f], Lambda([x], x <= f[x]))

lfp = define("lfp", [f], inf(prefixed(f)))
gfp = define("gfp", [f], sup(postfixed(f)))

prefixed_eval = prove(ForAll([f, x], prefixed(f)[x] == (f[x] <= x)), by=[prefixed.defn])
postfixed_eval = prove(
    ForAll([f, x], postfixed(f)[x] == (x <= f[x])), by=[postfixed.defn]
)


@Theorem(ForAll([f], Implies(monotone(f), f[lfp(f)] <= lfp(f))))
def lfp_prefixed(l):
    f = l.fix()
    l.intro()
    l.unfold(lfp)
    P = prefixed(f)

    l.apply(inf_greatest)
    l.unfold(is_lb)
    x = l.fix()
    l.intro()

    l.have(is_lb(P, inf(P)), by=[inf_is_lb(P)])
    l.unfold(is_lb, at=-1)
    l.specialize(-1, x)
    l.have(inf(P) <= x, by=[])

    l.unfold(monotone, at=0)
    l.specialize(0, inf(P), x)
    l.have(f[inf(P)] <= f[x], by=[])

    l.have(f[x] <= x, by=[prefixed_eval])
    l.auto(by=[le_trans])


@Theorem(ForAll([f], Implies(monotone(f), lfp(f) <= f[lfp(f)])))
def lfp_postfixed(l):
    f = l.fix()
    l.intro()
    l.unfold(lfp)
    P = prefixed(f)

    l.have(f[lfp(f)] <= lfp(f), by=[lfp_prefixed(f)])
    l.unfold(lfp, at=-1)

    l.unfold(monotone, at=0)
    l.specialize(0, f[inf(P)], inf(P))
    l.have(f[f[inf(P)]] <= f[inf(P)], by=[])

    l.have(prefixed(f)[f[inf(P)]], by=[prefixed_eval])

    l.have(is_lb(P, inf(P)), by=[inf_is_lb(P)])
    l.unfold(is_lb, at=-1)
    l.specialize(-1, f[inf(P)])
    l.have(inf(P) <= f[inf(P)], by=[])
    l.auto()


@Theorem(ForAll([f], Implies(monotone(f), f[lfp(f)] == lfp(f))))
def lfp_fixed(l):
    f = l.fix()
    l.intro()
    l.apply(le_antisym)
    l.have(f[lfp(f)] <= lfp(f), by=[lfp_prefixed(f)])
    l.have(lfp(f) <= f[lfp(f)], by=[lfp_postfixed(f)])
    l.auto()


@Theorem(
    ForAll(
        [f, x],
        Implies(And(monotone(f), f[x] == x), lfp(f) <= x),
    )
)
def lfp_least(l):
    f, x = l.fixes()
    l.intro()
    l.unfold(lfp)
    P = prefixed(f)

    l.have(prefixed(f)[x], by=[prefixed_eval, le_refl])

    l.have(is_lb(P, inf(P)), by=[inf_is_lb(P)])
    l.unfold(is_lb, at=-1)
    l.specialize(-1, x)
    l.have(inf(P) <= x, by=[])
    l.auto()


@Theorem(ForAll([f], Implies(monotone(f), gfp(f) <= f[gfp(f)])))
def gfp_postfixed(l):
    f = l.fix()
    l.intro()
    l.unfold(gfp)
    Q = postfixed(f)

    l.apply(sup_least)
    l.unfold(is_ub)
    x = l.fix()
    l.intro()

    l.have(is_ub(Q, sup(Q)), by=[sup_is_ub(Q)])
    l.unfold(is_ub, at=-1)
    l.specialize(-1, x)
    l.have(x <= sup(Q), by=[])

    l.unfold(monotone, at=0)
    l.specialize(0, x, sup(Q))
    l.have(f[x] <= f[sup(Q)], by=[])

    l.have(x <= f[x], by=[postfixed_eval])
    l.auto(by=[le_trans])


@Theorem(ForAll([f], Implies(monotone(f), f[gfp(f)] <= gfp(f))))
def gfp_prefixed(l):
    f = l.fix()
    l.intro()
    l.unfold(gfp)
    Q = postfixed(f)

    l.have(gfp(f) <= f[gfp(f)], by=[gfp_postfixed(f)])
    l.unfold(gfp, at=-1)

    l.unfold(monotone, at=0)
    l.specialize(0, sup(Q), f[sup(Q)])
    l.have(f[sup(Q)] <= f[f[sup(Q)]], by=[])

    l.have(postfixed(f)[f[sup(Q)]], by=[postfixed_eval])
    l.have(is_ub(Q, sup(Q)), by=[sup_is_ub(Q)])
    l.unfold(is_ub, at=-1)
    l.specialize(-1, f[sup(Q)])
    l.have(f[sup(Q)] <= sup(Q), by=[])
    l.auto()


@Theorem(ForAll([f], Implies(monotone(f), f[gfp(f)] == gfp(f))))
def gfp_fixed(l):
    f = l.fix()
    l.intro()
    l.apply(le_antisym)
    l.have(f[gfp(f)] <= gfp(f), by=[gfp_prefixed(f)])
    l.have(gfp(f) <= f[gfp(f)], by=[gfp_postfixed(f)])
    l.auto()


@Theorem(
    ForAll(
        [f, x],
        Implies(And(monotone(f), f[x] == x), x <= gfp(f)),
    )
)
def gfp_greatest(l):
    f, x = l.fixes()
    l.intro()
    l.unfold(gfp)
    Q = postfixed(f)

    l.have(postfixed(f)[x], by=[postfixed_eval, le_refl])

    l.have(is_ub(Q, sup(Q)), by=[sup_is_ub(Q)])
    l.unfold(is_ub, at=-1)
    l.specialize(-1, x)
    l.have(x <= sup(Q), by=[])
    l.auto()


@Theorem(
    ForAll(
        [f],
        Implies(
            monotone(f),
            And(
                f[lfp(f)] == lfp(f),
                f[gfp(f)] == gfp(f),
                QForAll([x], f[x] == x, lfp(f) <= x),
                QForAll([x], f[x] == x, x <= gfp(f)),
            ),
        ),
    )
)
def knaster_tarski(l):
    f = l.fix()
    l.intro()
    l.have(f[lfp(f)] == lfp(f), by=[lfp_fixed(f)])
    l.have(f[gfp(f)] == gfp(f), by=[gfp_fixed(f)])
    l.have(
        QForAll([x], f[x] == x, lfp(f) <= x),
        by=[lfp_least],
    )
    l.have(
        QForAll([x], f[x] == x, x <= gfp(f)),
        by=[gfp_greatest],
    )
    l.auto()


if __name__ == "__main__":
    print("knaster_tarski:", knaster_tarski)
