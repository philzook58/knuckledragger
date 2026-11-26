"""
Transfinite recursion on the ordinals (Halmos §18, §21).

`trec` needs a set X that holds every value in advance. Ordinal arithmetic
does not have one: α^β is defined from all earlier α^γ, and no set containing
them is available beforehand. With Replacement the codomain can be dropped,
for recursions G(δ, t) indexed by ordinals δ, where t is the sequence of
earlier values as a set of pairs:

- `is_rec_on(G, g, δ)`: g is a function on δ with g(γ) = G(γ, g restricted to γ).
- Uniqueness, by transfinite induction.
- Existence: the attempts on smaller ordinals agree, so their one-point
  extensions, collected by Replacement, unite into an attempt on δ.

`orec(G, δ)` is the attempt on δ, named with definite description, and
`oval(G, δ)` its value at δ. Then oval(G, δ) = G(δ, orec(G, δ)).
"""

from kdrag import Theorem, define, prove
from kdrag.smt import And, ArraySort, Consts, Exists, ForAll, Lambda, Not, Or
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import ZFSet, elem, le, pair, ran, sing, succ
from kdrag.contrib.zf.fun import (
    app,
    app_eq_of_pair_elem,
    elem_ran_of_pair_elem,
    is_func,
    pair_app_elem,
    pair_elem_prod,
)
from kdrag.contrib.zf.nat import elem_succ, elem_succ_self
from kdrag.contrib.zf.ordinal import (
    is_ordinal,
    is_ordinal_of_elem,
    is_ordinal_succ,
    repl,
    the,
    the_eq,
    elem_repl,
)
from kdrag.contrib.zf.ordset import (
    ordinal_comparable,
    ordinal_le_of_elem,
    ordinal_not_elem_self,
    ordinal_well_order,
)
from kdrag.contrib.zf.poset import nat_le_rel, seg, well_order_induction
from kdrag.contrib.zf.trec import elem_restrict_pair, restrict, restrict_le

D, E, a, b, c, g, h, p, x, y, z = Consts("D E a b c g h p x y z", ZFSet)
G = Consts("G", ArraySort(ZFSet, ZFSet, ZFSet))[0]

# g is a function on D, with no codomain given.
fn_on = define(
    "fn_on",
    [g, D],
    And(
        ForAll(p, elem(p, g), Exists([x, y], And(elem(x, D), p == pair(x, y)))),
        ForAll(x, elem(x, D), Exists(y, elem(pair(x, y), g))),
        ForAll([x, y, z], elem(pair(x, y), g), elem(pair(x, z), g), y == z),
    ),
)


@Theorem(ForAll([g, D], fn_on(g, D), is_func(g, D, ran(g))))
def is_func_of_fn_on(l):
    """Its range serves as a codomain."""
    g, D = l.fixes()
    l.intro()
    l.unfold(is_func)
    l.split()
    l.rw(le.defn)
    p0 = l.fix()
    l.intro()
    l.have(Exists([x, y], And(elem(x, D), p0 == pair(x, y))), by=[fn_on.defn(g, D)])
    (x0, y0), _ = l.obtain(-1)
    l.auto(by=[pair_elem_prod(x0, y0, D, ran(g)), elem_ran_of_pair_elem(x0, y0, g)])
    l.auto(by=[fn_on.defn(g, D)])
    l.auto(by=[fn_on.defn(g, D)])


app_eq_of_fn_on = prove(
    ForAll([g, D, x, y], fn_on(g, D), elem(pair(x, y), g), app(g, x) == y),
    by=[is_func_of_fn_on, app_eq_of_pair_elem],
)
pair_app_elem_of_fn_on = prove(
    ForAll([g, D, x], fn_on(g, D), elem(x, D), elem(pair(x, app(g, x)), g)),
    by=[is_func_of_fn_on, pair_app_elem],
)


fn_on_single = prove(
    ForAll(
        [g, D, x, y, z], fn_on(g, D), elem(pair(x, y), g), elem(pair(x, z), g), y == z
    ),
    by=[fn_on.defn],
)


@Theorem(ForAll([g, D, x, y], fn_on(g, D), elem(pair(x, y), g), elem(x, D)))
def elem_of_pair_elem_fn_on(l):
    g, D, x0, y0 = l.fixes()
    l.intros()
    l.have(
        Exists([x, y], And(elem(x, D), pair(x0, y0) == pair(x, y))),
        by=[fn_on.defn(g, D)],
    )
    (x1, y1), _ = l.obtain(-1)
    l.auto(by=[zf.pair_inj])


@Theorem(
    ForAll(
        [g, h, D],
        fn_on(g, D),
        fn_on(h, D),
        ForAll(x, elem(x, D), app(g, x) == app(h, x)),
        g == h,
    )
)
def fn_on_ext(l):
    """Functions on D with the same values are equal."""
    g, h, D = l.fixes()
    l.intros()
    l.rw(zf.ext_ax)
    p0 = l.fix()
    # p ∈ g is (x, g x) with x ∈ D, and (x, h x) ∈ h; the other way round too.
    l.have(
        ForAll(
            g,
            fn_on(g, D),
            elem(p0, g),
            Exists([x, y], And(elem(x, D), p0 == pair(x, y))),
        ),
        by=[fn_on.defn],
    )
    l.auto(by=[app_eq_of_fn_on, pair_app_elem_of_fn_on])


@Theorem(
    ForAll(
        [g, D, E],
        fn_on(g, D),
        E <= D,
        And(
            fn_on(restrict(g, E), E),
            ForAll(x, elem(x, E), app(restrict(g, E), x) == app(g, x)),
        ),
    )
)
def fn_on_restrict(l):
    """A function on D restricted to E ⊆ D is a function on E with the same values."""
    g, D, E = l.fixes()
    l.intros()
    gE = restrict(g, E)
    l.have(fn_on(gE, E))
    l.unfold(fn_on)
    l.split()
    l.fix()
    l.intro()
    l.auto(by=[restrict.defn(g, E), zf.elem_sep])
    x0 = l.fix()
    l.intro()
    l.auto(
        by=[
            pair_app_elem_of_fn_on(g, D, x0),
            elem_restrict_pair(g, E, x0, app(g, x0)),
            le.defn(E, D),
        ]
    )
    x1, y1, z1 = l.fixes()
    l.intros()
    l.auto(
        by=[
            elem_restrict_pair(g, E, x1, y1),
            elem_restrict_pair(g, E, x1, z1),
            fn_on.defn(g, D),
        ]
    )
    l.split()
    l.auto()
    x2 = l.fix()
    l.intro()
    l.auto(
        by=[
            pair_app_elem_of_fn_on(g, D, x2),
            elem_restrict_pair(g, E, x2, app(g, x2)),
            app_eq_of_fn_on(gE, E, x2, app(g, x2)),
            le.defn(E, D),
        ]
    )


# g is an attempt on D: a function on D with g(x) = G(x, g restricted to x).
is_rec_on = define(
    "is_rec_on",
    [G, g, D],
    And(fn_on(g, D), ForAll(x, elem(x, D), app(g, x) == G[x, restrict(g, x)])),
)


@Theorem(
    ForAll(
        [g, D, E, x],
        fn_on(g, D),
        E <= D,
        x <= E,
        restrict(restrict(g, E), x) == restrict(g, x),
    )
)
def restrict_restrict(l):
    g, D, E, x0 = l.fixes()
    l.intros()
    l.rw(zf.ext_ax)
    l.fix()
    l.auto(
        by=[
            restrict.defn(restrict(g, E), x0),
            restrict.defn(g, x0),
            restrict.defn(g, E),
            zf.elem_sep,
            le.defn(x0, E),
            zf.pair_inj,
        ]
    )


@Theorem(
    ForAll(
        [G, g, D, E],
        is_ordinal(D),
        is_ordinal(E),
        E <= D,
        is_rec_on(G, g, D),
        is_rec_on(G, restrict(g, E), E),
    )
)
def is_rec_on_restrict(l):
    """An attempt restricts to an attempt on a smaller ordinal."""
    G, g, D, E = l.fixes()
    l.intros()
    l.have(fn_on(g, D), by=[is_rec_on.defn(G, g, D)])
    l.have(
        And(
            fn_on(restrict(g, E), E),
            ForAll(x, elem(x, E), app(restrict(g, E), x) == app(g, x)),
        ),
        by=[fn_on_restrict(g, D, E)],
    )
    l.unfold(is_rec_on)
    l.split()
    l.auto()
    x0 = l.fix()
    l.intro()
    l.auto(
        by=[
            is_rec_on.defn(G, g, D),
            le.defn(E, D),
            restrict_restrict(g, D, E, x0),
            ordinal_le_of_elem(E, x0),
        ]
    )


@Theorem(
    ForAll([G, g, h, D], is_ordinal(D), is_rec_on(G, g, D), is_rec_on(G, h, D), g == h)
)
def is_rec_on_unique(l):
    """Halmos: two attempts on δ agree, by transfinite induction on δ."""
    G, g, h, D = l.fixes()
    l.intros()
    l.have(fn_on(g, D), by=[is_rec_on.defn(G, g, D)])
    l.have(fn_on(h, D), by=[is_rec_on.defn(G, h, D)])
    P = Lambda(x, app(g, x) == app(h, x))
    # If g and h agree below x, their restrictions to x are equal, so g x = h x.
    l.have(ForAll(a, elem(a, D), ForAll(b, elem(b, seg(nat_le_rel, D, a)), P[b]), P[a]))
    a0 = l.fix()
    l.intros()
    l.have(seg(nat_le_rel, D, a0) == a0, by=[is_ordinal.defn(D)])
    l.have(a0 <= D, by=[ordinal_le_of_elem(D, a0)])
    l.have(
        restrict(g, a0) == restrict(h, a0),
        by=[
            fn_on_ext(restrict(g, a0), restrict(h, a0), a0),
            fn_on_restrict(g, D, a0),
            fn_on_restrict(h, D, a0),
        ],
    )
    l.simp()
    l.auto(by=[is_rec_on.defn(G, g, D), is_rec_on.defn(G, h, D)])
    l.have(
        ForAll(a, elem(a, D), P[a]),
        by=[well_order_induction(nat_le_rel, D, P), ordinal_well_order(D)],
    )
    l.auto(by=[fn_on_ext(g, h, D)])


@Theorem(ForAll([g, D], fn_on(g, D), restrict(g, D) == g))
def restrict_self(l):
    g, D = l.fixes()
    l.intro()
    l.rw(zf.ext_ax)
    l.fix()
    l.auto(by=[restrict.defn(g, D), zf.elem_sep, fn_on.defn(g, D)])


@Theorem(
    ForAll(
        [g, a, b, x],
        Not(elem(a, x)),
        restrict(g | sing(pair(a, b)), x) == restrict(g, x),
    )
)
def restrict_union_sing(l):
    """Adding a pair outside x does not change the restriction to x."""
    g, a, b, x0 = l.fixes()
    l.intro()
    l.rw(zf.ext_ax)
    l.fix()
    l.auto(
        by=[
            restrict.defn(g | sing(pair(a, b)), x0),
            restrict.defn(g, x0),
            zf.elem_sep,
            zf.elem_union,
            zf.elem_sing,
            zf.pair_inj,
        ]
    )


@Theorem(
    ForAll(
        [G, g, D],
        is_ordinal(D),
        is_rec_on(G, g, D),
        is_rec_on(G, g | sing(pair(D, G[D, g])), succ(D)),
    )
)
def is_rec_on_succ(l):
    """An attempt on δ extends to δ⁺ by the value G(δ, g) at δ."""
    G, g, D = l.fixes()
    l.intros()
    v = G[D, g]
    g1 = g | sing(pair(D, v))
    l.have(fn_on(g, D), by=[is_rec_on.defn(G, g, D)])
    l.have(
        Not(elem(D, D)),
        by=[ordinal_not_elem_self(succ(D), D), is_ordinal_succ(D), elem_succ_self(D)],
    )
    mem = [zf.elem_union, zf.elem_sing, zf.pair_inj]
    l.have(fn_on(g1, succ(D)))
    l.unfold(fn_on)
    l.split()
    l.fix()
    l.intro()
    l.auto(by=[fn_on.defn(g, D), elem_succ] + mem)
    x0 = l.fix()
    l.intro()
    l.auto(by=[fn_on.defn(g, D), elem_succ(x0, D)] + mem)
    x1, y1, z1 = l.fixes()
    l.intros()
    # A pair of g has its first coordinate in δ, and δ ∉ δ.
    l.auto(
        by=[
            fn_on_single(g, D, x1, y1, z1),
            elem_of_pair_elem_fn_on(g, D, x1, y1),
            elem_of_pair_elem_fn_on(g, D, x1, z1),
            zf.elem_union(pair(x1, y1), g, sing(pair(D, v))),
            zf.elem_union(pair(x1, z1), g, sing(pair(D, v))),
            zf.elem_sing(pair(x1, y1), pair(D, v)),
            zf.elem_sing(pair(x1, z1), pair(D, v)),
            zf.pair_inj,
        ]
    )
    l.unfold(is_rec_on)
    l.split()
    l.auto()
    x2 = l.fix()
    l.intro()
    l.have(Or(elem(x2, D), x2 == D), by=[elem_succ(x2, D)])
    l.cases(elem(x2, D), x2 == D)
    # Below δ: same value, and δ is outside x, so the same restriction.
    l.have(Not(elem(D, x2)), by=[ordinal_le_of_elem(D, x2), le.defn(x2, D)])
    l.auto(
        by=[
            pair_app_elem_of_fn_on(g, D, x2),
            app_eq_of_fn_on(g1, succ(D), x2, app(g, x2)),
            zf.elem_union,
            restrict_union_sing(g, D, v, x2),
            is_rec_on.defn(G, g, D),
        ]
    )
    # At δ: the new value G(δ, g), and g restricted to δ is g.
    l.auto(
        by=[
            app_eq_of_fn_on(g1, succ(D), D, v),
            zf.elem_union,
            zf.elem_sing,
            restrict_union_sing(g, D, v, D),
            restrict_self(g, D),
        ]
    )


# The attempt on δ, its one-point extension to δ⁺, and the union of the
# extensions below δ.
orec = define("orec", [G, D], the(Lambda(g, is_rec_on(G, g, D))))
orec_ext = define("orec_ext", [G, D], orec(G, D) | sing(pair(D, G[D, orec(G, D)])))
orec_union = define(
    "orec_union", [G, D], zf.bigunion(repl(Lambda(x, orec_ext(G, x)), D))
)


@Theorem(
    ForAll(
        [G, D],
        is_ordinal(D),
        Exists(g, is_rec_on(G, g, D)),
        is_rec_on(G, orec(G, D), D),
    )
)
def orec_spec(l):
    G, D = l.fixes()
    l.intros()
    g0, _ = l.obtain(-1)
    P = Lambda(g, is_rec_on(G, g, D))
    l.have(ForAll(h, P[h], h == g0))
    h0 = l.fix()
    l.intro()
    l.simp(at=-1)
    l.auto(by=[is_rec_on_unique(G, h0, g0, D)])
    l.have(P[g0])
    l.simp()
    l.auto()
    l.unfold(orec)
    l.auto(by=[the_eq(P, g0)])


@Theorem(
    ForAll(
        [G, D, y],
        elem(y, repl(Lambda(x, orec_ext(G, x)), D))
        == Exists(x, And(elem(x, D), y == orec_ext(G, x))),
    )
)
def elem_repl_orec_ext(l):
    G, D, y0 = l.fixes()
    l.auto(by=[elem_repl(Lambda(x, orec_ext(G, x)), D, y0)])


@Theorem(
    ForAll(
        [G, D, p],
        elem(p, orec_union(G, D))
        == Exists(x, And(elem(x, D), elem(p, orec_ext(G, x)))),
    )
)
def elem_orec_union(l):
    G, D, p0 = l.fixes()
    l.unfold(orec_union)
    l.rw(zf.bigunion_ax)
    # p lies in some extension iff it lies in a member of the collection.
    l.split()
    l.intro()
    x1, _ = l.obtain(-1)
    l.exists(orec_ext(G, x1))
    l.have(Exists(x, And(elem(x, D), orec_ext(G, x1) == orec_ext(G, x))))
    l.exists(x1)
    l.auto()
    l.auto(by=[elem_repl_orec_ext(G, D, orec_ext(G, x1))])
    l.intro()
    B0, _ = l.obtain(-1)
    l.have(
        Exists(x, And(elem(x, D), B0 == orec_ext(G, x))),
        by=[elem_repl_orec_ext(G, D, B0)],
    )
    x0, _ = l.obtain(-1)
    l.exists(x0)
    l.auto()


@Theorem(
    ForAll(
        [g, h, D, E, x],
        fn_on(g, D),
        fn_on(h, E),
        h <= g,
        x <= E,
        restrict(g, x) == restrict(h, x),
    )
)
def restrict_eq_of_le(l):
    """A function h ⊆ g on E ⊇ x has the same restriction to x as g."""
    g, h, D, E, x0 = l.fixes()
    l.intros()
    l.rw(zf.ext_ax)
    l.fix()
    l.rw(restrict.defn(g, x0))
    l.rw(restrict.defn(h, x0))
    l.rw(zf.elem_sep)
    l.rw(zf.elem_sep)
    l.simp()
    l.split()
    l.intro()
    l.split(at=-1)
    (c0, d0), _ = l.obtain(4)
    # (c, h c) ∈ h ⊆ g, and g has one value at c.
    l.have(
        elem(pair(c0, app(h, c0)), h),
        by=[pair_app_elem_of_fn_on(h, E, c0), le.defn(x0, E)],
    )
    l.auto(by=[le.defn(h, g), fn_on_single(g, D, c0, d0, app(h, c0))])
    l.intro()
    l.auto(by=[le.defn(h, g)])


@Theorem(
    ForAll(
        [G, D],
        is_ordinal(D),
        Exists(g, is_rec_on(G, g, D)),
        is_rec_on(G, orec_ext(G, D), succ(D)),
    )
)
def orec_ext_rec_on(l):
    G, D = l.fixes()
    l.intros()
    l.auto(by=[orec_spec(G, D), is_rec_on_succ(G, orec(G, D), D), orec_ext.defn(G, D)])


@Theorem(
    ForAll(
        [G, x, y],
        is_ordinal(y),
        elem(x, succ(y)),
        is_rec_on(G, orec_ext(G, x), succ(x)),
        is_rec_on(G, orec_ext(G, y), succ(y)),
        orec_ext(G, x) <= orec_ext(G, y),
    )
)
def orec_ext_le(l):
    """The extensions grow: for ξ ≤ η, the one on ξ⁺ is the one on η⁺ cut down."""
    G, x0, y0 = l.fixes()
    l.intros()
    Sy = succ(y0)
    l.have(is_ordinal(Sy), by=[is_ordinal_succ(y0)])
    l.have(is_ordinal(x0), by=[is_ordinal_of_elem(Sy, x0)])
    l.have(is_ordinal(succ(x0)), by=[is_ordinal_succ(x0)])
    l.have(succ(x0) <= Sy, by=[ordinal_le_of_elem(Sy, x0), le.defn, elem_succ])
    ey = orec_ext(G, y0)
    l.have(
        is_rec_on(G, restrict(ey, succ(x0)), succ(x0)),
        by=[is_rec_on_restrict(G, ey, Sy, succ(x0))],
    )
    l.have(
        restrict(ey, succ(x0)) == orec_ext(G, x0),
        by=[is_rec_on_unique(G, restrict(ey, succ(x0)), orec_ext(G, x0), succ(x0))],
    )
    l.auto(by=[restrict_le(ey, succ(x0))])


@Theorem(
    ForAll(
        [G, D],
        is_ordinal(D),
        ForAll(x, elem(x, D), Exists(g, is_rec_on(G, g, x))),
        is_rec_on(G, orec_union(G, D), D),
    )
)
def orec_union_rec_on(l):
    """Halmos: if every ξ < δ carries an attempt, the extensions to ξ⁺ are nested,
    and their union is an attempt on δ."""
    G, D = l.fixes()
    l.intros()
    U = orec_union(G, D)

    def Ex(x):
        return orec_ext(G, x)

    l.have(
        ForAll(x, elem(x, D), is_rec_on(G, Ex(x), succ(x))),
        by=[orec_ext_rec_on, is_ordinal_of_elem],
    )
    l.have(ForAll(x, elem(x, D), fn_on(Ex(x), succ(x))), by=[is_rec_on.defn])
    l.have(
        ForAll(x, elem(x, D), succ(x) <= D), by=[ordinal_le_of_elem, le.defn, elem_succ]
    )
    # Any two extensions are nested, as ordinals are comparable.
    l.have(ForAll([x, y], elem(x, D), elem(y, D), Or(Ex(x) <= Ex(y), Ex(y) <= Ex(x))))
    x1, y1 = l.fixes()
    l.intros()
    l.auto(
        by=[
            is_ordinal_of_elem(D, x1),
            is_ordinal_of_elem(D, y1),
            ordinal_comparable(x1, y1),
            elem_succ(x1, y1),
            elem_succ(y1, x1),
            orec_ext_le(G, x1, y1),
            orec_ext_le(G, y1, x1),
        ]
    )
    l.have(ForAll(x, elem(x, D), Ex(x) <= U), by=[le.defn, elem_orec_union])
    l.have(fn_on(U, D))
    l.unfold(fn_on)
    l.split()
    p0 = l.fix()
    l.intro()
    l.have(Exists(x, And(elem(x, D), elem(p0, Ex(x)))), by=[elem_orec_union(G, D, p0)])
    x2, _ = l.obtain(-1)
    l.have(
        Exists([x, y], And(elem(x, succ(x2)), p0 == pair(x, y))),
        by=[fn_on.defn(Ex(x2), succ(x2))],
    )
    (a2, b2), _ = l.obtain(-1)
    l.exists(a2, b2)
    l.auto(by=[le.defn(succ(x2), D)])
    a3 = l.fix()
    l.intro()
    l.exists(app(Ex(a3), a3))
    l.auto(
        by=[
            pair_app_elem_of_fn_on(Ex(a3), succ(a3), a3),
            elem_succ_self(a3),
            le.defn(Ex(a3), U),
        ]
    )
    a4, b4, c4 = l.fixes()
    l.intros()
    l.have(Exists(x, And(elem(x, D), elem(pair(a4, b4), Ex(x)))), by=[elem_orec_union])
    x4, _ = l.obtain(-1)
    l.have(Exists(x, And(elem(x, D), elem(pair(a4, c4), Ex(x)))), by=[elem_orec_union])
    y4, _ = l.obtain(-1)
    # Both pairs lie in the larger extension, a function.
    l.auto(
        by=[
            le.defn(Ex(x4), Ex(y4)),
            le.defn(Ex(y4), Ex(x4)),
            fn_on_single(Ex(x4), succ(x4), a4, b4, c4),
            fn_on_single(Ex(y4), succ(y4), a4, b4, c4),
        ]
    )
    # U(a) is the extension's value, and U restricted to a is the extension's.
    l.unfold(is_rec_on)
    l.split()
    l.auto()
    a5 = l.fix()
    l.intro()
    E5 = Ex(a5)
    l.have(elem(a5, succ(a5)), by=[elem_succ_self(a5)])
    l.have(a5 <= succ(a5), by=[le.defn, elem_succ])
    l.have(
        app(U, a5) == app(E5, a5),
        by=[
            pair_app_elem_of_fn_on(E5, succ(a5), a5),
            le.defn(E5, U),
            app_eq_of_fn_on(U, D, a5, app(E5, a5)),
        ],
    )
    l.have(
        restrict(U, a5) == restrict(E5, a5),
        by=[restrict_eq_of_le(U, E5, D, succ(a5), a5)],
    )
    l.auto(by=[is_rec_on.defn(G, E5, succ(a5))])


@Theorem(ForAll([G, D], is_ordinal(D), Exists(g, is_rec_on(G, g, D))))
def exists_rec_on(l):
    """Every ordinal carries an attempt, by transfinite induction in δ⁺."""
    G, D = l.fixes()
    l.intro()
    S = succ(D)
    l.have(is_ordinal(S), by=[is_ordinal_succ(D)])
    P = Lambda(x, Exists(g, is_rec_on(G, g, x)))
    l.have(ForAll(a, elem(a, S), ForAll(b, elem(b, seg(nat_le_rel, S, a)), P[b]), P[a]))
    a0 = l.fix()
    l.intros()
    l.have(seg(nat_le_rel, S, a0) == a0, by=[is_ordinal.defn(S)])
    l.simp()
    l.exists(orec_union(G, a0))
    l.auto(by=[orec_union_rec_on(G, a0), is_ordinal_of_elem(S, a0)])
    l.have(
        ForAll(a, elem(a, S), P[a]),
        by=[well_order_induction(nat_le_rel, S, P), ordinal_well_order(S)],
    )
    l.have(P[D], by=[elem_succ_self(D)])
    l.simp(at=-1)
    l.auto()


orec_rec_on = prove(
    ForAll([G, D], is_ordinal(D), is_rec_on(G, orec(G, D), D)),
    by=[orec_spec, exists_rec_on],
)
fn_on_orec = prove(
    ForAll([G, D], is_ordinal(D), fn_on(orec(G, D), D)),
    by=[orec_rec_on, is_rec_on.defn],
)

# The value at δ, computed from the earlier values.
oval = define("oval", [G, D], G[D, orec(G, D)])


@Theorem(
    ForAll([G, D, x], is_ordinal(D), elem(x, D), restrict(orec(G, D), x) == orec(G, x))
)
def restrict_orec(l):
    G, D, x0 = l.fixes()
    l.intros()
    g0 = orec(G, D)
    l.have(is_ordinal(x0), by=[is_ordinal_of_elem(D, x0)])
    l.have(
        is_rec_on(G, restrict(g0, x0), x0),
        by=[
            is_rec_on_restrict(G, g0, D, x0),
            orec_rec_on(G, D),
            ordinal_le_of_elem(D, x0),
        ],
    )
    l.auto(
        by=[is_rec_on_unique(G, restrict(g0, x0), orec(G, x0), x0), orec_rec_on(G, x0)]
    )


@Theorem(ForAll([G, D, x], is_ordinal(D), elem(x, D), app(orec(G, D), x) == oval(G, x)))
def app_orec(l):
    """Halmos §18 without a codomain: the sequence on δ has the value G(ξ, earlier
    values) at each ξ < δ."""
    G, D, x0 = l.fixes()
    l.intros()
    l.auto(
        by=[
            orec_rec_on(G, D),
            is_rec_on.defn(G, orec(G, D), D),
            restrict_orec(G, D, x0),
            oval.defn(G, x0),
        ]
    )
