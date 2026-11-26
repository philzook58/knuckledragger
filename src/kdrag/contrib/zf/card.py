"""
Comparing sizes of sets (Halmos §22): the Schröder-Bernstein theorem.

`dominated(X, Y)` (Halmos' X ≾ Y) holds when X maps one-to-one into Y.
The proof follows Halmos: X_X, the elements of X with a parentless ancestor
in X, is the smallest set containing X - G[Y] and closed under x ↦ G(F x).
F matches X_X with its image, and G⁻¹ matches the rest of X with the rest of Y.
No choice is used.
"""

from kdrag import Theorem, define, prove
from kdrag.smt import And, ArraySort, Consts, Exists, ForAll, If, Lambda, Not
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import ZFSet, elem, le, pow, sep, sing
from kdrag.contrib.zf.fun import (
    bij_on,
    elem_sinter,
    elem_sub,
    inj_on,
    maps_to,
    sinter,
    surj_on,
)
from kdrag.contrib.zf.finite import equivalent, image, inv, inv_apply

C, X, Y, Z, k, x, x1, y = Consts("C X Y Z k x x1 y", ZFSet)
F, G = Consts("F G", ArraySort(ZFSet, ZFSet))

dominated = define("dominated", [X, Y], Exists(F, And(maps_to(F, X, Y), inj_on(F, X))))

# Halmos' X_X: the parentless elements X - G[Y] and all their descendants in X.
desc_closed = define(
    "desc_closed",
    [C, F, G, X, Y],
    And(X - image(G, Y, X) <= C, ForAll(x, elem(x, C), elem(G[F[x]], C))),
)
origin_x = define(
    "origin_x", [F, G, X, Y], sinter(sep(pow(X), Lambda(C, desc_closed(C, F, G, X, Y))))
)


def _maps(F, G, X, Y):
    return [maps_to(F, X, Y), maps_to(G, Y, X)]


@Theorem(ForAll([F, G, X, Y], *_maps(F, G, X, Y), desc_closed(X, F, G, X, Y)))
def desc_closed_self(l):
    """X itself contains the orphans and is closed, so the family defining X_X is nonempty."""
    F, G, X, Y = l.fixes()
    l.intros()
    l.unfold(desc_closed)
    l.auto(by=[le.defn, elem_sub, maps_to.defn(F, X, Y), maps_to.defn(G, Y, X)])


@Theorem(
    ForAll(
        [F, G, X, Y, x],
        *_maps(F, G, X, Y),
        elem(x, origin_x(F, G, X, Y))
        == ForAll(C, C <= X, desc_closed(C, F, G, X, Y), elem(x, C)),
    )
)
def elem_origin_x(l):
    F, G, X, Y, x = l.fixes()
    l.intros()
    l.unfold(origin_x)
    fam = sep(pow(X), Lambda(C, desc_closed(C, F, G, X, Y)))
    l.have(
        elem(X, fam),
        by=[zf.elem_sep, zf.elem_pow, le.defn, desc_closed_self(F, G, X, Y)],
    )
    l.have(fam != zf.emp, by=[zf.elem_emp])
    l.auto(by=[elem_sinter(fam, x), zf.elem_sep, zf.elem_pow])


@Theorem(
    ForAll(
        [F, G, X, Y, C],
        *_maps(F, G, X, Y),
        C <= X,
        desc_closed(C, F, G, X, Y),
        origin_x(F, G, X, Y) <= C,
    )
)
def origin_x_le_of_closed(l):
    """X_X is the smallest such set."""
    F, G, X, Y, C = l.fixes()
    l.intros()
    l.unfold(le)
    x = l.fix()
    l.auto(by=[elem_origin_x(F, G, X, Y, x)])


origin_x_le = prove(
    ForAll([F, G, X, Y], *_maps(F, G, X, Y), origin_x(F, G, X, Y) <= X),
    by=[origin_x_le_of_closed, desc_closed_self, le.defn],
)


@Theorem(
    ForAll(
        [F, G, X, Y], *_maps(F, G, X, Y), desc_closed(origin_x(F, G, X, Y), F, G, X, Y)
    )
)
def origin_x_closed(l):
    """X_X contains the orphans and the descendants of its elements."""
    F, G, X, Y = l.fixes()
    l.intros()
    l.unfold(desc_closed)
    l.split()
    l.auto(by=[le.defn, elem_origin_x, desc_closed.defn])
    l.fix()
    l.auto(by=[elem_origin_x, desc_closed.defn])


@Theorem(
    ForAll(
        [F, G, X, Y, x],
        *_maps(F, G, X, Y),
        elem(x, origin_x(F, G, X, Y)),
        elem(x, image(G, Y, X)),
        Exists(x1, And(elem(x1, origin_x(F, G, X, Y)), G[F[x1]] == x)),
    )
)
def exists_parent_origin_x(l):
    """An element of X_X with a parent descends from an element of X_X."""
    F, G, X, Y, x = l.fixes()
    D = origin_x(F, G, X, Y)
    l.intros()
    l.contra()
    # Otherwise D - {x} still contains the orphans (x has a parent) and is closed
    # (no descendant step lands on x), so the smallest such set D is inside D - {x}.
    l.have(
        desc_closed(D - sing(x), F, G, X, Y),
        by=[
            desc_closed.defn,
            origin_x_closed(F, G, X, Y),
            le.defn,
            elem_sub,
            zf.elem_sing,
        ],
    )
    l.have(D - sing(x) <= X, by=[origin_x_le(F, G, X, Y), le.defn, elem_sub])
    l.have(D <= D - sing(x), by=[origin_x_le_of_closed(F, G, X, Y, D - sing(x))])
    l.auto(by=[le.defn(D, D - sing(x)), elem_sub, zf.elem_sing])


@Theorem(ForAll([X, Y], dominated(X, Y), dominated(Y, X), equivalent(X, Y)))
def schroeder_bernstein(l):
    """Halmos §22: if X ≾ Y and Y ≾ X, then X ~ Y."""
    X, Y = l.fixes()
    l.intros()
    l.unfold(dominated, at=0)
    l.unfold(dominated, at=1)
    F0, _ = l.obtain(0)
    G0, _ = l.obtain(1)
    D = origin_x(F0, G0, X, Y)
    Ginv = inv(G0, Y)
    l.have(D <= X, by=[origin_x_le(F0, G0, X, Y)])
    l.have(desc_closed(D, F0, G0, X, Y), by=[origin_x_closed(F0, G0, X, Y)])

    # Outside X_X every x has a parent y = G⁻¹ x in Y.
    l.have(
        ForAll(x, elem(x, X), Not(elem(x, D)), And(elem(Ginv[x], Y), G0[Ginv[x]] == x))
    )
    x0 = l.fix()
    l.intros()
    l.have(
        elem(x0, image(G0, Y, X)),
        by=[desc_closed.defn(D, F0, G0, X, Y), le.defn, elem_sub],
    )
    l.have(Exists(y, And(elem(y, Y), G0[y] == x0)), by=[image.defn, zf.elem_sep])
    y0, _ = l.obtain(-1)
    l.auto(by=[inv_apply(G0, Y, y0)])

    # Halmos: F on X_X, and G⁻¹ on the elements of X that originate in Y or nowhere.
    H = Lambda(x, If(elem(x, D), F0[x], Ginv[x]))
    l.unfold(equivalent)
    l.exists(H)
    l.unfold(bij_on)
    l.split()
    l.auto(by=[maps_to.defn(H, X, Y), maps_to.defn(F0, X, Y), le.defn])
    # One-to-one: F and G⁻¹ are each one-to-one, and F x1 = G⁻¹ x2 with x1 ∈ X_X
    # would put x2 = G(F x1) in X_X.
    l.unfold(inj_on)
    x1, x2 = l.fixes()
    l.intros()
    l.auto(by=[inj_on.defn(F0, X), desc_closed.defn(D, F0, G0, X, Y), le.defn])
    # Onto: if G y ∈ X_X it is G(F x1) for some x1 ∈ X_X, so y = F x1;
    # otherwise y = G⁻¹(G y).
    l.unfold(surj_on)
    y1 = l.fix()
    l.intro()
    l.cases(elem(G0[y1], D), Not(elem(G0[y1], D)))
    l.have(
        elem(G0[y1], image(G0, Y, X)),
        by=[image.defn, zf.elem_sep, maps_to.defn(G0, Y, X)],
    )
    l.have(
        Exists(x1, And(elem(x1, D), G0[F0[x1]] == G0[y1])),
        by=[exists_parent_origin_x(F0, G0, X, Y, G0[y1])],
    )
    x3, _ = l.obtain(-1)
    l.exists(x3)
    l.auto(by=[inj_on.defn(G0, Y), maps_to.defn(F0, X, Y), le.defn])
    l.exists(G0[y1])
    l.auto(by=[inv_apply(G0, Y, y1), maps_to.defn(G0, Y, X)])


@Theorem(ForAll([X, Y, Z], dominated(X, Y), dominated(Y, Z), dominated(X, Z)))
def dominated_trans(l):
    """Compose the one-to-one maps."""
    X, Y, Z = l.fixes()
    l.intros()
    l.unfold(dominated, at=0)
    l.unfold(dominated, at=1)
    F0, _ = l.obtain(0)
    G0, _ = l.obtain(1)
    l.unfold(dominated)
    l.exists(Lambda(k, G0[F0[k]]))
    l.auto(by=[maps_to.defn, inj_on.defn])


@Theorem(ForAll([X, Y], Y <= X, dominated(Y, X)))
def dominated_of_le(l):
    X, Y = l.fixes()
    l.intro()
    l.unfold(dominated)
    l.exists(Lambda(k, k))
    l.auto(by=[maps_to.defn, inj_on.defn, le.defn])


dominated_of_equivalent = prove(
    ForAll([X, Y], equivalent(X, Y), dominated(X, Y)),
    by=[equivalent.defn, bij_on.defn, dominated.defn],
)
