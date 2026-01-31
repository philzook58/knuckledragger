from kdrag.all import *


# for line_profiler
# @profile
def test_sheffer():
    simp = []
    Stroke = smt.DeclareSort("Stroke")
    x, y, z, a, b, d = smt.Consts("x y z a b d", Stroke)
    nand = smt.Function("nand", Stroke, Stroke, Stroke)
    kd.notation.or_.register(Stroke, nand)

    # prime is "not"
    invert = kd.define("inv", [x], x | x)
    kd.notation.invert.register(Stroke, invert)

    sh1 = kd.axiom(smt.ForAll([a], ~(~a) == a))
    sh2 = kd.axiom(smt.ForAll([a, b], a | (b | ~b) == ~a))
    sh3 = kd.axiom(smt.ForAll([a, b, d], ~(a | (b | d)) == (~b | a) | (~d | a)))

    c = kd.Calc([a, b], a | b)
    c.eq(~(~(a | b)), by=[sh1])
    c.eq(~(~(a | (~(~b)))), by=sh1)
    c.eq(~~(~~b | a), by=[sh3, invert.defn])
    c.eq((~~b) | a, by=[sh1])
    c.eq(b | a, by=[sh1])
    commut = c.qed()

    c = kd.Calc([a, b], a | ~a)
    c.eq(~~(a | ~a), by=sh1)
    c.eq(~((a | ~a) | (b | ~b)), by=sh2)
    c.eq(~((b | ~b) | (a | ~a)), by=commut)
    c.eq(~~(b | ~b), by=sh2)
    c.eq(b | ~b, by=sh1)
    all_bot = c.qed()

    inf = kd.define("inf", [a, b], ~a | ~b)
    sup = kd.define("sup", [a, b], ~(a | b))

    bot = kd.define("bot", [], a | ~a)
    top = kd.define("top", [], ~bot)

    inf_comm = kd.prove(
        smt.ForAll([a, b], inf(a, b) == inf(b, a)), by=[inf.defn, commut]
    )
    sup_comm = kd.prove(
        smt.ForAll([a, b], sup(a, b) == sup(b, a)), by=[sup.defn, commut]
    )

    ident1 = kd.prove(
        smt.ForAll([a], sup(a, bot) == a), by=[sup.defn, bot.defn, sh1, sh2]
    )
    ident2 = kd.prove(
        smt.ForAll([a], inf(a, top) == a), by=[inf.defn, top.defn, bot.defn, sh1, sh2]
    )

    distrib1 = kd.prove(
        smt.ForAll([a, b, d], sup(a, inf(b, d)) == inf(sup(a, b), sup(a, d))),
        by=[inf.defn, sup.defn, sh1, sh3, commut],
    )
    distrib2 = kd.prove(
        smt.ForAll([a, b, d], inf(a, sup(b, d)) == sup(inf(a, b), inf(a, d))),
        by=[inf.defn, sup.defn, sh1, sh3, commut],
    )

    compl1 = kd.prove(
        smt.ForAll([a], sup(a, ~a) == top),
        by=[sup.defn, top.defn, bot.defn, sh1, sh2, all_bot],
    )
    compl2 = kd.prove(
        smt.ForAll([a], inf(a, ~a) == bot), by=[inf.defn, bot.defn, sh1, sh2, all_bot]
    )

    simp += [ident1, ident2, compl1, compl2]

    c = kd.Calc([a], sup(a, top))
    c.eq(inf(sup(a, top), top), by=ident2)
    c.eq(inf(top, sup(a, top)), by=inf_comm)
    c.eq(inf(sup(a, ~a), sup(a, top)), by=compl1)
    c.eq(sup(a, inf(~a, top)), by=distrib1)
    c.eq(sup(a, ~a), by=ident2)
    c.eq(top, by=compl1)
    bound1 = c.qed()

    # this is where I first started talking to chatgpt

    c = kd.Calc([a], inf(a, bot))
    c.eq(sup(inf(a, bot), bot), by=ident1)
    c.eq(sup(bot, inf(a, bot)), by=sup_comm)
    c.eq(sup(inf(a, ~a), inf(a, bot)), by=compl2)
    c.eq(inf(a, sup(~a, bot)), by=distrib2)
    c.eq(inf(a, ~a), by=ident1)
    c.eq(bot, by=compl2)
    bound2 = c.qed()

    c = kd.Calc([a, b], sup(a, inf(a, b)))
    c.eq(sup(inf(a, top), inf(a, b)), by=ident2)
    c.eq(inf(a, sup(top, b)), by=distrib2)
    c.eq(inf(a, sup(b, top)), by=sup_comm)
    c.eq(inf(a, top), by=bound1)
    c.eq(a, by=ident2)
    absorb1 = c.qed()

    c = kd.Calc([a, b], inf(a, sup(a, b)))
    c.eq(inf(sup(a, bot), sup(a, b)), by=ident1)
    c.eq(sup(a, inf(bot, b)), by=distrib1)
    c.eq(sup(a, inf(b, bot)), by=inf_comm)
    c.eq(sup(a, bot), by=bound2)
    c.eq(a, by=ident1)
    absorb2 = c.qed()

    c = kd.Calc([a], a)
    c.eq(inf(a, sup(a, bot)), by=absorb2)  # Rewrite using absorb2: a ⊓ (a ⊔ bot) = a
    c.eq(inf(a, a), by=ident1)  # Simplify sup(a, bot) = a using ident1
    idemp2 = c.qed()

    simp += [bound1, bound2, absorb1, absorb2, idemp2]

    l = kd.Lemma(kd.QForAll([a, b], sup(a, b) == top, inf(a, b) == bot, b == ~a))
    _a, _b = l.fixes()
    l.intros()
    l.symm()
    l.eq(inf(_b, top), by=[ident2])
    l.eq(inf(_b, sup(_a, ~_a)), by=[compl1])
    l.eq(sup(inf(_b, _a), inf(_b, ~_a)), by=[distrib2])
    l.eq(sup(inf(_a, _b), inf(~_a, _b)), by=[inf_comm])
    l.eq(sup(bot, inf(~_a, _b)))
    l.eq(sup(inf(_a, ~_a), inf(~_a, _b)), by=[compl2])
    l.eq(sup(inf(~_a, _a), inf(~_a, _b)), by=[inf_comm])
    l.eq(inf(~_a, sup(_a, _b)), by=[distrib2])
    l.eq(inf(~_a, top))
    l.eq(~_a, by=[ident2])
    l.auto()
    inv = l.qed()

    l = kd.Lemma(kd.QForAll([a], ~~a == a))
    _a = l.fix()
    l.symm()
    l.apply(inv)
    l.auto(by=[inf_comm, sup_comm, compl1, compl2])
    dne = l.qed()

    l = kd.Lemma(kd.QForAll([a, b], ~a == ~b, a == b))
    _a, _b = l.fixes()
    l.intros()
    l.have(~~_a == ~~_b, by=[])
    l.rw(dne, at=-1)
    l.auto(by=dne(_a))
    inv_elim = l.qed()

    l = kd.Lemma(kd.QForAll([a, b], sup(a, ~b) == top, inf(a, ~b) == bot, a == b))
    _a, _b = l.fixes()
    l.intros()
    l.have(~_b == ~_a, by=[inv])
    l.apply(inv_elim)
    l.auto()
    cancel = l.qed()

    c = kd.Calc([a, b], sup(a, sup(~a, b)))
    c.eq(
        inf(sup(a, sup(~a, b)), top), by=ident2
    )  # Rewrite: a ⊔ (¬a ⊔ b) = (a ⊔ (¬a ⊔ b)) ⊓ u
    c.eq(
        inf(top, sup(a, sup(~a, b))), by=inf_comm
    )  # Commute: u ⊓ (a ⊔ (¬a ⊔ b)) -> (a ⊔ (¬a ⊔ b)) ⊓ u
    c.eq(inf(sup(a, ~a), sup(a, sup(~a, b))), by=compl1)  # Replace a ⊔ ¬a = u
    c.eq(sup(a, inf(~a, sup(~a, b))), by=distrib1)  # Distribute sup over inf
    c.eq(sup(a, ~a), by=[absorb2, compl1])  # Simplify: ¬a ⊓ (¬a ⊔ b) = ¬a
    c.eq(top, by=compl1)  # Simplify a ⊔ ¬a = u
    A1 = c.qed()

    # c = kd.Calc([a,b], inf(a, sup(~a, b)) == bot)
    c = kd.Calc([a, b], inf(a, inf(~a, b)))
    c.eq(
        sup(inf(a, inf(~a, b)), bot), by=ident1
    )  # Rewrite: a ⊓ (¬a ⊓ b) = (a ⊓ (¬a ⊓ b)) ⊔ z
    c.eq(
        sup(bot, inf(a, inf(~a, b))), by=sup_comm
    )  # Commute: z ⊔ (a ⊓ (¬a ⊓ b)) -> (a ⊓ (¬a ⊓ b)) ⊔ z
    c.eq(sup(inf(a, ~a), inf(a, inf(~a, b))), by=compl2)  # Replace a ⊓ ¬a = z
    c.eq(inf(a, sup(~a, inf(~a, b))), by=distrib2)  # Distribute inf over sup
    c.eq(inf(a, ~a), by=[absorb1, compl2])  # Simplify: ¬a ⊔ (¬a ⊓ b) = ¬a
    c.eq(bot, by=compl2)  # Simplify a ⊓ ¬a = z
    A2 = c.qed()

    simp += [A1, A2]

    c = kd.Lemma(smt.ForAll([a, b], ~sup(a, b) == inf(~a, ~b)))
    _a, _b = c.fixes()
    c.symm()
    c.apply(cancel)  # Hmm. apply should already apply split?
    c.split()

    # First case
    c.rw(dne)
    c.rw(sup_comm)
    c.rw(distrib1)
    # c
    c.auto(by=[dne(_a), dne(_b), A1, inf_comm, sup_comm, ident2])

    # c.rw(distrib2)
    # from kdrag.solvers import VampireSolver, TweeSolver, EProverTHFSolver

    c.auto(by=[A1, A2, inf_comm, distrib2, sup_comm, ident1] + simp)
    dm1 = c.qed()

    l = kd.Lemma(smt.ForAll([a, b], ~inf(a, b) == sup(~a, ~b)))
    _a, _b = l.fixes()
    l.symm()
    l.apply(cancel)
    l.split()

    l.auto(by=[A1, A2, inf_comm, distrib2, sup_comm, ident1] + simp)
    l.auto(by=[dne(_a), dne(_b), A2, inf_comm, distrib2, sup_comm, ident1] + simp)
    dm2 = l.qed()

    simp += [dm1, dm2]

    D1 = kd.prove(
        smt.ForAll([a, b, d], sup(sup(a, sup(b, d)), ~a) == top),
        by=[sup_comm, ident2, distrib1, compl1] + simp,
    )

    E1 = kd.prove(
        smt.ForAll([a, b, d], inf(b, sup(a, sup(b, d))) == b),
        by=[distrib2, absorb2, sup_comm, absorb1],
    )

    E2 = kd.prove(
        smt.ForAll([a, b, d], sup(b, inf(a, inf(b, d))) == b),
        by=[distrib1, absorb1, inf_comm, absorb2],
    )

    c = kd.Calc([a, b, d], sup(sup(a, sup(b, d)), ~b))
    c.eq(
        sup(~b, sup(a, sup(b, d))), by=sup_comm
    )  # Commute: (a ⊔ (b ⊔ c)) ⊔ bᶜ -> bᶜ ⊔ (a ⊔ (b ⊔ c))
    c.eq(
        inf(top, sup(~b, sup(a, sup(b, d)))), by=[inf_comm] + simp
    )  # Rewrite: u ⊓ (bᶜ ⊔ (a ⊔ (b ⊔ c)))
    c.eq(inf(sup(b, ~b), sup(~b, sup(a, sup(b, d)))), by=simp)  # Substitute u = b ⊔ bᶜ
    c.eq(
        inf(sup(~b, b), sup(~b, sup(a, sup(b, d)))), by=sup_comm
    )  # Commute: (b ⊔ bᶜ) -> (bᶜ ⊔ b)
    c.eq(sup(~b, inf(b, sup(a, sup(b, d)))), by=distrib1)  # Distribute inf over sup
    c.eq(sup(~b, b), by=E1)  # Simplify using E₁: b ⊓ (a ⊔ (b ⊔ c)) = b
    c.eq(top, by=[sup_comm] + simp)  # Substitute: bᶜ ⊔ b = u
    F1 = c.qed()

    c = kd.Calc([a, b, d], sup(sup(a, sup(b, d)), ~d))
    c.eq(
        sup(sup(a, sup(d, b)), ~d), by=sup_comm
    )  # Apply commutativity to reorder (b ⊔ c) -> (c ⊔ b)
    # Apply F₁: (a ⊔ (c ⊔ b)) ⊔ cᶜ = u
    c.eq(top, by=F1)  # Substitute: cᶜ ⊔ (a ⊔ (c ⊔ b)) = u
    G1 = c.qed()

    c = smt.Const("c", Stroke)

    d = kd.Calc([a, b, c], inf(~sup(sup(a, b), c), a))
    d.eq(inf(a, inf(inf(~a, ~b), ~c)), by=simp + [inf_comm])
    d.eq(sup(inf(a, inf(inf(~a, ~b), ~c)), bot), by=ident1)  # Rewrite using identity
    d.eq(
        sup(bot, inf(a, inf(inf(~a, ~b), ~c))), by=sup_comm
    )  # Commute bot ⊔ (...) -> (...) ⊔ bot
    d.eq(
        sup(inf(a, ~a), inf(a, inf(inf(~a, ~b), ~c))), by=compl2
    )  # Substitute a ⊓ ¬a = z
    d.eq(inf(a, sup(~a, inf(inf(~a, ~b), ~c))), by=distrib2)  # Distribute inf over sup
    d.eq(
        inf(a, sup(~a, inf(~c, inf(~a, ~b)))), by=inf_comm
    )  # Reorder terms: (~b ⊓ (~a ⊓ ~c)) -> (~a ⊓ (~c ⊓ ~b))
    d.eq(inf(a, ~a), by=E2)  # Apply E₂: ¬a ⊔ (¬a ⊓ (¬c ⊓ ¬b)) = ¬a
    d.eq(bot, by=compl2)  # Simplify a ⊓ ¬a = z
    H1 = d.qed()

    d = kd.Calc([a, b, c], inf(~sup(sup(a, b), c), b))
    d.eq(inf(~sup(sup(b, a), c), b), by=sup_comm)  # Reorder: (a ⊔ b ⊔ c) -> (b ⊔ a ⊔ c)
    d.eq(bot, by=H1)  # Apply \( H₁ \): \( \neg (b \lor a \lor c) \land b = z \)
    I1 = d.qed()

    d = kd.Calc([a, b, c], inf(~sup(sup(a, b), c), c))

    J1 = kd.prove(
        smt.ForAll([a, b, c], inf(~sup(sup(a, b), c), c) == bot),
        by=[sup_comm, inf_comm] + simp,
    )

    l = kd.Lemma(smt.ForAll([a, b, c], sup(a, sup(b, c)) == sup(sup(a, b), c)))
    _a, _b, _c = l.fixes()
    l.apply(cancel)
    l.split()

    l.auto(by=[distrib1, D1, F1, G1] + simp)
    l.auto(by=[distrib2, inf_comm, H1, I1, J1] + simp)
    assoc1 = l.qed()

    simp += [assoc1]

    assoc2 = kd.prove(
        smt.ForAll([a, b, c], inf(a, inf(b, c)) == inf(inf(a, b), c)),
        by=[inv_elim] + simp,
    )

    le = kd.define("le", [a, b], a == inf(b, a))
    kd.notation.le.register(Stroke, le)

    le_trans = kd.prove(
        kd.QForAll([a, b, c], a <= b, b <= c, a <= c), by=[assoc2, le.defn]
    )

    le_antisym = kd.prove(
        kd.QForAll([a, b], a <= b, b <= a, a == b), by=[le.defn, inf_comm]
    )


if __name__ == "__main__":
    test_sheffer()
