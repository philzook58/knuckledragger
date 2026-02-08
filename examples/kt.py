import kdrag as kd
import kdrag.smt as smt

# Declare an abstract complete lattice
L = smt.DeclareSort("L")
SetL = smt.SetSort(L)

x, y, z = smt.Consts("x y z", L)
A, B = smt.Consts("A B", SetL)

le = smt.Function("le", L, L, smt.BoolSort())
kd.notation.le.register(L, le)

le_refl = kd.axiom(smt.ForAll([x], x <= x))
le_trans = kd.axiom(smt.ForAll([x, y, z], smt.Implies(smt.And(x <= y, y <= z), x <= z)))
le_antisym = kd.axiom(smt.ForAll([x, y], smt.Implies(smt.And(x <= y, y <= x), x == y)))

is_ub = kd.define("is_ub", [A, y], kd.QForAll([x], A[x], x <= y))
is_lb = kd.define("is_lb", [A, y], kd.QForAll([x], A[x], y <= x))

sup = smt.Function("sup", SetL, L)
inf = smt.Function("inf", SetL, L)

sup_is_ub = kd.axiom(smt.ForAll([A], is_ub(A, sup(A))))
sup_least = kd.axiom(smt.ForAll([A, y], smt.Implies(is_ub(A, y), sup(A) <= y)))

inf_is_lb = kd.axiom(smt.ForAll([A], is_lb(A, inf(A))))
inf_greatest = kd.axiom(smt.ForAll([A, y], smt.Implies(is_lb(A, y), y <= inf(A))))

# Monotone functions on L (represented as arrays L -> L)
FSort = smt.ArraySort(L, L)
f = smt.Const("f", FSort)

monotone = kd.define(
    "monotone", [f], smt.ForAll([x, y], smt.Implies(x <= y, f[x] <= f[y]))
)

prefixed = kd.define("prefixed", [f], smt.Lambda([x], f[x] <= x))
postfixed = kd.define("postfixed", [f], smt.Lambda([x], x <= f[x]))

lfp = kd.define("lfp", [f], inf(prefixed(f)))
gfp = kd.define("gfp", [f], sup(postfixed(f)))

prefixed_eval = kd.prove(
    smt.ForAll([f, x], prefixed(f)[x] == (f[x] <= x)), by=[prefixed.defn]
)
postfixed_eval = kd.prove(
    smt.ForAll([f, x], postfixed(f)[x] == (x <= f[x])), by=[postfixed.defn]
)


@kd.Theorem(smt.ForAll([f], smt.Implies(monotone(f), f[lfp(f)] <= lfp(f))))
def lfp_prefixed(l):
    f = l.fix()
    l.intros()
    l.unfold(lfp)
    P = prefixed(f)

    l.apply(inf_greatest)
    l.unfold(is_lb)
    x = l.fix()
    l.intros()

    l.have(is_lb(P, inf(P)), by=[inf_is_lb(P)])
    l.unfold(is_lb, at=-1)
    l.specialize(-1, x)
    l.have(inf(P) <= x, by=[])

    l.unfold(monotone, at=0)
    l.specialize(0, inf(P), x)
    l.have(f[inf(P)] <= f[x], by=[])

    l.have(f[x] <= x, by=[prefixed_eval])
    l.auto(by=[le_trans])


@kd.Theorem(smt.ForAll([f], smt.Implies(monotone(f), lfp(f) <= f[lfp(f)])))
def lfp_postfixed(l):
    f = l.fix()
    l.intros()
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


@kd.Theorem(smt.ForAll([f], smt.Implies(monotone(f), f[lfp(f)] == lfp(f))))
def lfp_fixed(l):
    f = l.fix()
    l.intros()
    l.apply(le_antisym)
    l.have(f[lfp(f)] <= lfp(f), by=[lfp_prefixed(f)])
    l.have(lfp(f) <= f[lfp(f)], by=[lfp_postfixed(f)])
    l.auto()


@kd.Theorem(
    smt.ForAll(
        [f, x],
        smt.Implies(smt.And(monotone(f), f[x] == x), lfp(f) <= x),
    )
)
def lfp_least(l):
    f, x = l.fixes()
    l.intros()
    l.unfold(lfp)
    P = prefixed(f)

    l.have(prefixed(f)[x], by=[prefixed_eval, le_refl])

    l.have(is_lb(P, inf(P)), by=[inf_is_lb(P)])
    l.unfold(is_lb, at=-1)
    l.specialize(-1, x)
    l.have(inf(P) <= x, by=[])
    l.auto()


@kd.Theorem(smt.ForAll([f], smt.Implies(monotone(f), gfp(f) <= f[gfp(f)])))
def gfp_postfixed(l):
    f = l.fix()
    l.intros()
    l.unfold(gfp)
    Q = postfixed(f)

    l.apply(sup_least)
    l.unfold(is_ub)
    x = l.fix()
    l.intros()

    l.have(is_ub(Q, sup(Q)), by=[sup_is_ub(Q)])
    l.unfold(is_ub, at=-1)
    l.specialize(-1, x)
    l.have(x <= sup(Q), by=[])

    l.unfold(monotone, at=0)
    l.specialize(0, x, sup(Q))
    l.have(f[x] <= f[sup(Q)], by=[])

    l.have(x <= f[x], by=[postfixed_eval])
    l.auto(by=[le_trans])


@kd.Theorem(smt.ForAll([f], smt.Implies(monotone(f), f[gfp(f)] <= gfp(f))))
def gfp_prefixed(l):
    f = l.fix()
    l.intros()
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


@kd.Theorem(smt.ForAll([f], smt.Implies(monotone(f), f[gfp(f)] == gfp(f))))
def gfp_fixed(l):
    f = l.fix()
    l.intros()
    l.apply(le_antisym)
    l.have(f[gfp(f)] <= gfp(f), by=[gfp_prefixed(f)])
    l.have(gfp(f) <= f[gfp(f)], by=[gfp_postfixed(f)])
    l.auto()


@kd.Theorem(
    smt.ForAll(
        [f, x],
        smt.Implies(smt.And(monotone(f), f[x] == x), x <= gfp(f)),
    )
)
def gfp_greatest(l):
    f, x = l.fixes()
    l.intros()
    l.unfold(gfp)
    Q = postfixed(f)

    l.have(postfixed(f)[x], by=[postfixed_eval, le_refl])

    l.have(is_ub(Q, sup(Q)), by=[sup_is_ub(Q)])
    l.unfold(is_ub, at=-1)
    l.specialize(-1, x)
    l.have(x <= sup(Q), by=[])
    l.auto()


@kd.Theorem(
    smt.ForAll(
        [f],
        smt.Implies(
            monotone(f),
            smt.And(
                f[lfp(f)] == lfp(f),
                f[gfp(f)] == gfp(f),
                kd.QForAll([x], f[x] == x, lfp(f) <= x),
                kd.QForAll([x], f[x] == x, x <= gfp(f)),
            ),
        ),
    )
)
def knaster_tarski(l):
    f = l.fix()
    l.intros()
    l.have(f[lfp(f)] == lfp(f), by=[lfp_fixed(f)])
    l.have(f[gfp(f)] == gfp(f), by=[gfp_fixed(f)])
    l.have(
        kd.QForAll([x], f[x] == x, lfp(f) <= x),
        by=[lfp_least],
    )
    l.have(
        kd.QForAll([x], f[x] == x, x <= gfp(f)),
        by=[gfp_greatest],
    )
    l.auto()


if __name__ == "__main__":
    print("knaster_tarski:", knaster_tarski)
