"""
Cardinal arithmetic (Halmos §24), stated for sets up to equivalence.

The sum X + Y is the disjoint union `osum_set(X, Y)` = X × {0} ∪ Y × {1}, the
product is X × Y, and the power Y^X is the set `funs(X, Y)` of functions from
X to Y. The associative and distributive laws reuse the similarities built for
ordinal arithmetic, since a similarity is in particular a one-to-one
correspondence. Cantor's theorem says X is strictly dominated by P(X) ~ 2^X.
No choice is used.
"""

from kdrag import Theorem, define
from kdrag.smt import And, ArraySort, BoolSort, Consts, Exists, ForAll, If, Lambda, Not
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import ZFSet, elem, le, pair, pow, prod, sep, sing, zero
from kdrag.contrib.zf.card import dominated
from kdrag.contrib.zf.finite import equivalent, equivalent_of_inverse
from kdrag.contrib.zf.fun import (
    app,
    app_elem,
    app_graph,
    bij_on,
    elem_prod_iff,
    eq_graph,
    graph,
    inj_on,
    is_func,
    is_func_graph,
    maps_to,
    pair_elem_prod,
    pfst,
    pfst_pair,
    psnd,
    psnd_pair,
    surj_on,
)
from kdrag.contrib.zf.oarith import osum_assoc_map, osum_rel, similarity_osum_assoc
from kdrag.contrib.zf.omul import (
    odist_map,
    oprod_assoc_map,
    oprod_rel,
    similarity_odist,
    similarity_oprod_assoc,
)
from kdrag.contrib.zf.poset import nat_le_rel
from kdrag.contrib.zf.sim import equivalent_of_similarity
from kdrag.contrib.zf.dsum import elem_osum_set, inl, inr, osum_set
from kdrag.contrib.zf.nat import elem_two, one, two, zero_ne_one
from kdrag.contrib.zf._sep import define_sep

A, B, C, X, Y, Z, f, g, p, x, y = Consts("A B C X Y Z f g p x y", ZFSet)
F = Consts("F", ArraySort(ZFSet, ZFSet))[0]
R, S, T = Consts("R S T", ArraySort(ZFSet, ZFSet, BoolSort()))
L = nat_le_rel  # any relation will do below


@Theorem(ForAll([A, B, C], equivalent(osum_set(osum_set(A, B), C), osum_set(A, osum_set(B, C)))))
def sum_assoc_equivalent(l):
    """(a + b) + c = a + (b + c)."""
    A, B, C = l.fixes()
    l.auto(
        by=[
            similarity_osum_assoc(L, L, L, A, B, C),
            equivalent_of_similarity(
                osum_assoc_map,
                osum_rel(osum_rel(L, L), L),
                osum_set(osum_set(A, B), C),
                osum_rel(L, osum_rel(L, L)),
                osum_set(A, osum_set(B, C)),
            ),
        ]
    )


@Theorem(ForAll([A, B, C], equivalent(prod(prod(A, B), C), prod(A, prod(B, C)))))
def prod_assoc_equivalent(l):
    """(ab)c = a(bc)."""
    A, B, C = l.fixes()
    l.auto(
        by=[
            similarity_oprod_assoc(L, L, L, A, B, C),
            equivalent_of_similarity(
                oprod_assoc_map,
                oprod_rel(oprod_rel(L, L), L),
                prod(prod(A, B), C),
                oprod_rel(L, oprod_rel(L, L)),
                prod(A, prod(B, C)),
            ),
        ]
    )


@Theorem(ForAll([A, B, C], equivalent(prod(A, osum_set(B, C)), osum_set(prod(A, B), prod(A, C)))))
def prod_sum_distrib_equivalent(l):
    """a(b + c) = ab + ac."""
    A, B, C = l.fixes()
    l.auto(
        by=[
            similarity_odist(L, L, L, A, B, C),
            equivalent_of_similarity(
                odist_map,
                oprod_rel(L, osum_rel(L, L)),
                prod(A, osum_set(B, C)),
                osum_rel(oprod_rel(L, L), oprod_rel(L, L)),
                osum_set(prod(A, B), prod(A, C)),
            ),
        ]
    )


# Swapping the tags or the coordinates is its own inverse.
swap_tag = Lambda(p, If(p == inl(pfst(p)), inr(pfst(p)), inl(pfst(p))))
swap = Lambda(p, pair(psnd(p), pfst(p)))


@Theorem(ForAll([A, B], equivalent(osum_set(A, B), osum_set(B, A))))
def sum_comm_equivalent(l):
    """a + b = b + a: swap the tags."""
    A, B = l.fixes()
    _tags = [elem_osum_set, pfst_pair, zero_ne_one, zf.pair_inj]
    l.have(maps_to(swap_tag, osum_set(A, B), osum_set(B, A)), by=[maps_to.defn] + _tags)
    l.have(maps_to(swap_tag, osum_set(B, A), osum_set(A, B)), by=[maps_to.defn] + _tags)
    l.auto(by=[equivalent_of_inverse(swap_tag, swap_tag, osum_set(A, B), osum_set(B, A))] + _tags)


@Theorem(ForAll([A, B], equivalent(prod(A, B), prod(B, A))))
def prod_comm_equivalent(l):
    """ab = ba: swap the coordinates."""
    A, B = l.fixes()
    _pairs = [elem_prod_iff, pair_elem_prod, pfst_pair, psnd_pair]
    l.have(maps_to(swap, prod(A, B), prod(B, A)), by=[maps_to.defn] + _pairs)
    l.have(maps_to(swap, prod(B, A), prod(A, B)), by=[maps_to.defn] + _pairs)
    l.auto(by=[equivalent_of_inverse(swap, swap, prod(A, B), prod(B, A))] + _pairs)


@Theorem(ForAll(X, dominated(X, pow(X))))
def dominated_pow(l):
    """x ↦ {x}."""
    X = l.fix()
    l.unfold(dominated)
    l.exists(Lambda(x, sing(x)))
    l.split()
    l.unfold(maps_to)
    x0 = l.fix()
    l.intro()
    l.simp()
    l.have(sing(x0) <= X, by=[le.defn, zf.elem_sing])
    l.auto(by=[zf.elem_pow(X, sing(x0))])
    l.unfold(inj_on)
    x0, y0 = l.fixes()
    l.intros()
    l.simp(at=-1)
    l.auto(by=[zf.elem_sing(x0, x0), zf.elem_sing(x0, y0)])


# Cantor's diagonal set for F : P(X) → X.
diag, elem_diag = define_sep(
    "diag", [F, X], X, x, Exists(A, And(A <= X, F[A] == x, Not(elem(x, A))))
)


@Theorem(ForAll(X, Not(dominated(pow(X), X))))
def cantor_injective(l):
    """Halmos §24, Cantor's theorem: P(X) does not map one-to-one into X. Given
    such an F, let D = {F(A) | A ⊆ X, F(A) ∉ A}. Then F(D) ∈ D iff F(D) ∉ D."""
    X = l.fix()
    l.intro()
    l.unfold(dominated, at=0)
    F0, _ = l.obtain(0)
    D = diag(F0, X)
    l.have(D <= X, by=[le.defn, elem_diag])
    l.have(elem(D, pow(X)), by=[zf.elem_pow])
    d = F0[D]
    l.have(elem(d, X), by=[maps_to.defn(F0, pow(X), X)])
    # d ∈ D means d = F(A) ∉ A for some A, and then A = D.
    l.auto(by=[elem_diag(F0, X, d), inj_on.defn(F0, pow(X)), zf.elem_pow])


# Halmos' Y^X: the set of functions from X to Y.
funs = define("funs", [X, Y], sep(pow(prod(X, Y)), Lambda(f, is_func(f, X, Y))))


@Theorem(ForAll([X, Y, f], elem(f, funs(X, Y)) == is_func(f, X, Y)))
def elem_funs(l):
    l.fixes()
    l.unfold(funs)
    l.rw(zf.elem_sep)
    l.simp()
    l.auto(by=[zf.elem_pow, is_func.defn])


# The characteristic function of A ⊆ X, and the set where f is 1.
chi_fn = define("chi_fn", [A], Lambda(x, If(elem(x, A), one, zero)))
chi = define("chi", [A, X], graph(chi_fn(A), X, two))
ones, elem_ones = define_sep("ones", [f, X], X, x, app(f, x) == one)


@Theorem(ForAll([A, X], And(maps_to(chi_fn(A), X, two), is_func(chi(A, X), X, two))))
def is_func_chi(l):
    A, X = l.fixes()
    l.have(maps_to(chi_fn(A), X, two), by=[maps_to.defn, chi_fn.defn, elem_two])
    l.auto(by=[chi.defn, is_func_graph(chi_fn(A), X, two)])


@Theorem(ForAll([A, X, x], elem(x, X), app(chi(A, X), x) == If(elem(x, A), one, zero)))
def app_chi(l):
    A, X, x0 = l.fixes()
    l.intro()
    l.have(maps_to(chi_fn(A), X, two), by=[is_func_chi(A, X)])
    l.auto(by=[chi.defn, app_graph(chi_fn(A), X, two, x0), chi_fn.defn])


@Theorem(ForAll(X, equivalent(pow(X), funs(X, two))))
def pow_equivalent_funs_two(l):
    """Halmos §24: P(X) ~ 2^X, by A ↦ the characteristic function of A."""
    X = l.fix()
    l.unfold(equivalent)
    l.exists(Lambda(A, chi(A, X)))
    l.unfold(bij_on)
    l.split()
    l.unfold(maps_to)
    l.fix()
    l.intro()
    l.simp()
    l.auto(by=[elem_funs, is_func_chi])
    # Equal characteristic functions agree at each x ∈ X, and 0 ≠ 1.
    l.unfold(inj_on)
    A0, B0 = l.fixes()
    l.intros()
    l.simp(at=-1)
    l.rw(zf.ext_ax)
    x0 = l.fix()
    l.cases(elem(x0, X), Not(elem(x0, X)))
    l.auto(by=[app_chi(A0, X, x0), app_chi(B0, X, x0), zero_ne_one])
    l.auto(by=[zf.elem_pow, le.defn])
    # f is the characteristic function of the set where it is 1.
    l.unfold(surj_on)
    f0 = l.fix()
    l.intro()
    A1 = ones(f0, X)
    l.exists(A1)
    l.have(A1 <= X, by=[le.defn, elem_ones])
    l.have(is_func(f0, X, two), by=[elem_funs])
    l.have(ForAll(x, elem(x, X), app(f0, x) == chi_fn(A1)[x]))
    x1 = l.fix()
    l.intro()
    l.auto(by=[chi_fn.defn, elem_ones(f0, X, x1), app_elem(f0, X, two, x1), elem_two])
    l.simp()
    l.auto(by=[zf.elem_pow, chi.defn, eq_graph(f0, chi_fn(A1), X, two)])


@Theorem(
    ForAll(
        [f, g, X, Y],
        is_func(f, X, Y),
        is_func(g, X, Y),
        ForAll(x, elem(x, X), app(f, x) == app(g, x)),
        f == g,
    )
)
def func_ext(l):
    """Functions with the same values are equal: both are the graph of them."""
    f, g, X, Y = l.fixes()
    l.intros()
    G = Lambda(x, app(g, x))
    l.auto(by=[eq_graph(f, G, X, Y), eq_graph(g, G, X, Y)])


# a^(b + c) = a^b · a^c: f ↦ (f ∘ inl, f ∘ inr), with inverse by cases.
app_inl = define("app_inl", [f], Lambda(x, app(f, inl(x))))
app_inr = define("app_inr", [f], Lambda(x, app(f, inr(x))))
cases_fn = define(
    "cases_fn", [f, g], Lambda(p, If(p == inl(pfst(p)), app(f, pfst(p)), app(g, pfst(p))))
)


@Theorem(
    ForAll(
        [f, X, Z, Y],
        is_func(f, osum_set(X, Z), Y),
        And(maps_to(app_inl(f), X, Y), maps_to(app_inr(f), Z, Y)),
    )
)
def maps_to_app_inl_inr(l):
    f, X, Z, Y = l.fixes()
    l.intro()
    l.split()
    l.unfold(maps_to)
    x0 = l.fix()
    l.intro()
    l.auto(
        by=[
            app_inl.defn,
            app_elem(f, osum_set(X, Z), Y, inl(x0)),
            elem_osum_set(X, Z, inl(x0)),
            pfst_pair,
        ]
    )
    l.unfold(maps_to)
    x0 = l.fix()
    l.intro()
    l.auto(
        by=[
            app_inr.defn,
            app_elem(f, osum_set(X, Z), Y, inr(x0)),
            elem_osum_set(X, Z, inr(x0)),
            pfst_pair,
            zf.pair_inj,
            zero_ne_one,
        ]
    )


@Theorem(ForAll([X, Z, Y], equivalent(funs(osum_set(X, Z), Y), prod(funs(X, Y), funs(Z, Y)))))
def power_add_equivalent(l):
    """Halmos §24: a^(b + c) = a^b · a^c."""
    X, Z, Y = l.fixes()
    S = osum_set(X, Z)

    def phi(f):
        return pair(graph(app_inl(f), X, Y), graph(app_inr(f), Z, Y))

    l.unfold(equivalent)
    l.exists(Lambda(f, phi(f)))
    l.unfold(bij_on)
    l.split()
    l.unfold(maps_to)
    f0 = l.fix()
    l.intro()
    l.simp()
    l.have(is_func(f0, S, Y), by=[elem_funs])
    l.auto(
        by=[
            maps_to_app_inl_inr(f0, X, Z, Y),
            is_func_graph(app_inl(f0), X, Y),
            is_func_graph(app_inr(f0), Z, Y),
            elem_funs,
            pair_elem_prod,
        ]
    )
    # Equal restrictions: f and g agree on each (x, 0) and (z, 1).
    l.unfold(inj_on)
    f0, g0 = l.fixes()
    l.intros()
    l.simp(at=-1)
    l.have(is_func(f0, S, Y), by=[elem_funs])
    l.have(is_func(g0, S, Y), by=[elem_funs])
    l.have(maps_to(app_inl(f0), X, Y), by=[maps_to_app_inl_inr(f0, X, Z, Y)])
    l.have(maps_to(app_inr(f0), Z, Y), by=[maps_to_app_inl_inr(f0, X, Z, Y)])
    l.have(maps_to(app_inl(g0), X, Y), by=[maps_to_app_inl_inr(g0, X, Z, Y)])
    l.have(maps_to(app_inr(g0), Z, Y), by=[maps_to_app_inl_inr(g0, X, Z, Y)])
    l.have(ForAll(p, elem(p, S), app(f0, p) == app(g0, p)))
    p0 = l.fix()
    l.intro()
    x0 = pfst(p0)
    l.auto(
        by=[
            elem_osum_set(X, Z, p0),
            zf.pair_inj,
            app_graph(app_inl(f0), X, Y, x0),
            app_graph(app_inl(g0), X, Y, x0),
            app_graph(app_inr(f0), Z, Y, x0),
            app_graph(app_inr(g0), Z, Y, x0),
            app_inl.defn,
            app_inr.defn,
        ]
    )
    l.auto(by=[func_ext(f0, g0, S, Y)])
    # Given (g, h), define f by cases; its restrictions are g and h.
    l.unfold(surj_on)
    q0 = l.fix()
    l.intro()
    g1, h1 = pfst(q0), psnd(q0)
    l.have(
        And(is_func(g1, X, Y), is_func(h1, Z, Y), q0 == pair(g1, h1)),
        by=[elem_prod_iff(funs(X, Y), funs(Z, Y), q0), elem_funs],
    )
    K = cases_fn(g1, h1)
    l.have(maps_to(K, S, Y))
    l.unfold(maps_to)
    p1 = l.fix()
    l.intro()
    l.auto(
        by=[
            cases_fn.defn,
            elem_osum_set(X, Z, p1),
            app_elem(g1, X, Y, pfst(p1)),
            app_elem(h1, Z, Y, pfst(p1)),
            zf.pair_inj,
            zero_ne_one,
        ]
    )
    f1 = graph(K, S, Y)
    l.have(is_func(f1, S, Y), by=[is_func_graph(K, S, Y)])
    l.exists(f1)
    l.simp()
    l.have(maps_to(app_inl(f1), X, Y), by=[maps_to_app_inl_inr(f1, X, Z, Y)])
    l.have(maps_to(app_inr(f1), Z, Y), by=[maps_to_app_inl_inr(f1, X, Z, Y)])
    l.have(ForAll(x, elem(x, X), app(g1, x) == app_inl(f1)[x]))
    x1 = l.fix()
    l.intro()
    l.auto(
        by=[
            app_inl.defn,
            app_graph(K, S, Y, inl(x1)),
            elem_osum_set(X, Z, inl(x1)),
            cases_fn.defn,
            pfst_pair,
        ]
    )
    l.have(ForAll(x, elem(x, Z), app(h1, x) == app_inr(f1)[x]))
    x1 = l.fix()
    l.intro()
    l.auto(
        by=[
            app_inr.defn,
            app_graph(K, S, Y, inr(x1)),
            elem_osum_set(X, Z, inr(x1)),
            cases_fn.defn,
            pfst_pair,
            zf.pair_inj,
            zero_ne_one,
        ]
    )
    l.auto(by=[elem_funs, eq_graph(g1, app_inl(f1), X, Y), eq_graph(h1, app_inr(f1), Z, Y)])


# (ab)^c = a^c · b^c: f ↦ (pfst ∘ f, psnd ∘ f), with inverse x ↦ (g x, h x).
app_fst = define("app_fst", [f], Lambda(x, pfst(app(f, x))))
app_snd = define("app_snd", [f], Lambda(x, psnd(app(f, x))))
pair_fn = define("pair_fn", [f, g], Lambda(x, pair(app(f, x), app(g, x))))


@Theorem(
    ForAll(
        [f, X, Y, Z],
        is_func(f, X, prod(Y, Z)),
        And(maps_to(app_fst(f), X, Y), maps_to(app_snd(f), X, Z)),
    )
)
def maps_to_app_fst_snd(l):
    f, X, Y, Z = l.fixes()
    l.intro()
    l.have(ForAll(x, elem(x, X), elem(app(f, x), prod(Y, Z))))
    x0 = l.fix()
    l.intro()
    l.auto(by=[app_elem(f, X, prod(Y, Z), x0)])
    l.unfold(maps_to)
    l.auto(by=[app_fst.defn, app_snd.defn, elem_prod_iff])


@Theorem(ForAll([X, Y, Z], equivalent(funs(X, prod(Y, Z)), prod(funs(X, Y), funs(X, Z)))))
def mul_power_equivalent(l):
    """Halmos §24: (ab)^c = a^c · b^c."""
    X, Y, Z = l.fixes()
    P = prod(Y, Z)

    def phi(f):
        return pair(graph(app_fst(f), X, Y), graph(app_snd(f), X, Z))

    l.unfold(equivalent)
    l.exists(Lambda(f, phi(f)))
    l.unfold(bij_on)
    l.split()
    l.unfold(maps_to)
    f0 = l.fix()
    l.intro()
    l.simp()
    l.have(is_func(f0, X, P), by=[elem_funs])
    l.auto(
        by=[
            maps_to_app_fst_snd(f0, X, Y, Z),
            is_func_graph(app_fst(f0), X, Y),
            is_func_graph(app_snd(f0), X, Z),
            elem_funs,
            pair_elem_prod,
        ]
    )
    # Equal coordinate functions: the values agree as pairs.
    l.unfold(inj_on)
    f0, g0 = l.fixes()
    l.intros()
    l.simp(at=-1)
    l.have(is_func(f0, X, P), by=[elem_funs])
    l.have(is_func(g0, X, P), by=[elem_funs])
    l.have(
        And(maps_to(app_fst(f0), X, Y), maps_to(app_snd(f0), X, Z)),
        by=[maps_to_app_fst_snd(f0, X, Y, Z)],
    )
    l.have(
        And(maps_to(app_fst(g0), X, Y), maps_to(app_snd(g0), X, Z)),
        by=[maps_to_app_fst_snd(g0, X, Y, Z)],
    )
    l.have(ForAll(x, elem(x, X), app(f0, x) == app(g0, x)))
    x0 = l.fix()
    l.intro()
    l.auto(
        by=[
            zf.pair_inj,
            app_graph(app_fst(f0), X, Y, x0),
            app_graph(app_fst(g0), X, Y, x0),
            app_graph(app_snd(f0), X, Z, x0),
            app_graph(app_snd(g0), X, Z, x0),
            app_fst.defn,
            app_snd.defn,
            app_elem(f0, X, P, x0),
            app_elem(g0, X, P, x0),
            elem_prod_iff(Y, Z, app(f0, x0)),
            elem_prod_iff(Y, Z, app(g0, x0)),
        ]
    )
    l.auto(by=[func_ext(f0, g0, X, P)])
    # Given (g, h), x ↦ (g x, h x) has coordinates g and h.
    l.unfold(surj_on)
    q0 = l.fix()
    l.intro()
    g1, h1 = pfst(q0), psnd(q0)
    l.have(
        And(is_func(g1, X, Y), is_func(h1, X, Z), q0 == pair(g1, h1)),
        by=[elem_prod_iff(funs(X, Y), funs(X, Z), q0), elem_funs],
    )
    K = pair_fn(g1, h1)
    l.have(maps_to(K, X, P), by=[maps_to.defn, pair_fn.defn, app_elem, pair_elem_prod])
    f1 = graph(K, X, P)
    l.have(is_func(f1, X, P), by=[is_func_graph(K, X, P)])
    l.exists(f1)
    l.simp()
    l.have(
        And(maps_to(app_fst(f1), X, Y), maps_to(app_snd(f1), X, Z)),
        by=[maps_to_app_fst_snd(f1, X, Y, Z)],
    )
    l.have(ForAll(x, elem(x, X), app(f1, x) == pair(app(g1, x), app(h1, x))))
    x1 = l.fix()
    l.intro()
    l.auto(by=[app_graph(K, X, P, x1), pair_fn.defn])
    l.have(ForAll(x, elem(x, X), app(g1, x) == app_fst(f1)[x]), by=[app_fst.defn, pfst_pair])
    l.have(ForAll(x, elem(x, X), app(h1, x) == app_snd(f1)[x]), by=[app_snd.defn, psnd_pair])
    l.auto(by=[elem_funs, eq_graph(g1, app_fst(f1), X, Y), eq_graph(h1, app_snd(f1), X, Z)])


# (a^b)^c = a^(bc): h ↦ ((x, z) ↦ h(z)(x)), with inverse z ↦ (x ↦ k(x, z)).
uncurry = define("uncurry", [f], Lambda(p, app(app(f, psnd(p)), pfst(p))))
slice_fn = define("slice_fn", [f, y], Lambda(x, app(f, pair(x, y))))
curry = define("curry", [f, X, Y], Lambda(y, graph(slice_fn(f, y), X, Y)))


@Theorem(ForAll([f, X, Y, Z], is_func(f, Z, funs(X, Y)), maps_to(uncurry(f), prod(X, Z), Y)))
def maps_to_uncurry(l):
    f, X, Y, Z = l.fixes()
    l.intro()
    l.unfold(maps_to)
    p0 = l.fix()
    l.intro()
    z0 = psnd(p0)
    l.have(
        elem(app(f, z0), funs(X, Y)), by=[elem_prod_iff(X, Z, p0), app_elem(f, Z, funs(X, Y), z0)]
    )
    l.auto(
        by=[uncurry.defn, elem_funs, elem_prod_iff(X, Z, p0), app_elem(app(f, z0), X, Y, pfst(p0))]
    )


@Theorem(
    ForAll(
        [f, X, Y, Z],
        is_func(f, prod(X, Z), Y),
        ForAll(
            y,
            elem(y, Z),
            And(maps_to(slice_fn(f, y), X, Y), is_func(graph(slice_fn(f, y), X, Y), X, Y)),
        ),
    )
)
def is_func_slice(l):
    f, X, Y, Z = l.fixes()
    l.intro()
    z0 = l.fix()
    l.intro()
    l.have(
        maps_to(slice_fn(f, z0), X, Y), by=[maps_to.defn, slice_fn.defn, app_elem, pair_elem_prod]
    )
    l.auto(by=[is_func_graph(slice_fn(f, z0), X, Y)])


@Theorem(ForAll([X, Y, Z], equivalent(funs(Z, funs(X, Y)), funs(prod(X, Z), Y))))
def power_mul_equivalent(l):
    """Halmos §24: (a^b)^c = a^(bc)."""
    X, Y, Z = l.fixes()
    W = prod(X, Z)
    FXY = funs(X, Y)
    l.unfold(equivalent)
    l.exists(Lambda(f, graph(uncurry(f), W, Y)))
    l.unfold(bij_on)
    l.split()
    l.unfold(maps_to)
    f0 = l.fix()
    l.intro()
    l.simp()
    l.auto(by=[elem_funs, maps_to_uncurry(f0, X, Y, Z), is_func_graph(uncurry(f0), W, Y)])
    # Equal uncurried graphs: h₁(z)(x) = h₂(z)(x) for all x, z.
    l.unfold(inj_on)
    f0, g0 = l.fixes()
    l.intros()
    l.simp(at=-1)
    l.have(is_func(f0, Z, FXY), by=[elem_funs])
    l.have(is_func(g0, Z, FXY), by=[elem_funs])
    l.have(maps_to(uncurry(f0), W, Y), by=[maps_to_uncurry(f0, X, Y, Z)])
    l.have(maps_to(uncurry(g0), W, Y), by=[maps_to_uncurry(g0, X, Y, Z)])
    l.have(ForAll(y, elem(y, Z), app(f0, y) == app(g0, y)))
    z0 = l.fix()
    l.intro()
    l.have(ForAll(x, elem(x, X), app(app(f0, z0), x) == app(app(g0, z0), x)))
    x0 = l.fix()
    l.intro()
    p0 = pair(x0, z0)
    l.auto(
        by=[
            pair_elem_prod(x0, z0, X, Z),
            app_graph(uncurry(f0), W, Y, p0),
            app_graph(uncurry(g0), W, Y, p0),
            uncurry.defn,
            pfst_pair,
            psnd_pair,
        ]
    )
    l.auto(
        by=[
            func_ext(app(f0, z0), app(g0, z0), X, Y),
            elem_funs,
            app_elem(f0, Z, FXY, z0),
            app_elem(g0, Z, FXY, z0),
        ]
    )
    l.auto(by=[func_ext(f0, g0, Z, FXY)])
    # Given k on X × Z, curry it: z ↦ (x ↦ k(x, z)).
    l.unfold(surj_on)
    k0 = l.fix()
    l.intro()
    l.have(is_func(k0, W, Y), by=[elem_funs])
    C = curry(k0, X, Y)
    l.have(maps_to(C, Z, FXY), by=[maps_to.defn, curry.defn, elem_funs, is_func_slice(k0, X, Y, Z)])
    h1 = graph(C, Z, FXY)
    l.have(is_func(h1, Z, FXY), by=[is_func_graph(C, Z, FXY)])
    l.exists(h1)
    l.simp()
    l.have(maps_to(uncurry(h1), W, Y), by=[maps_to_uncurry(h1, X, Y, Z)])
    l.have(ForAll(p, elem(p, W), app(k0, p) == uncurry(h1)[p]))
    p1 = l.fix()
    l.intro()
    x1, z1 = pfst(p1), psnd(p1)
    l.have(And(elem(x1, X), elem(z1, Z), p1 == pair(x1, z1)), by=[elem_prod_iff(X, Z, p1)])
    l.have(app(h1, z1) == graph(slice_fn(k0, z1), X, Y), by=[app_graph(C, Z, FXY, z1), curry.defn])
    l.have(
        app(graph(slice_fn(k0, z1), X, Y), x1) == app(k0, pair(x1, z1)),
        by=[is_func_slice(k0, X, Y, Z), app_graph(slice_fn(k0, z1), X, Y, x1), slice_fn.defn],
    )
    l.auto(by=[uncurry.defn])
    l.auto(by=[elem_funs, eq_graph(k0, uncurry(h1), W, Y)])
