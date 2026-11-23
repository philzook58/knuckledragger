"""
Functions as sets of ordered pairs (Halmos §8).

A function is its graph. `app(f, x)` reads the value at `x` without choice,
as `⋃{y | (x, y) ∈ f}` (Isabelle/ZF's `apply`); off the domain it is junk.
"""

from kdrag import Theorem, define, prove
from kdrag.smt import And, Consts, Exists, ForAll, Lambda, Not
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import (
    ZFSet,
    bigunion,
    elem,
    le,
    pair,
    prod,
    ran,
    sep,
    sing,
    upair,
)
from kdrag.theories.zf.prod_lemmas import elem_prod_strong

A, B, X, Y, f, x, y, z = Consts("A B X Y f x y z", ZFSet)

# Small set facts missing from theories.zf

elem_sub = prove(
    ForAll([x, A, B], elem(x, A - B) == And(elem(x, A), Not(elem(x, B)))),
    by=[zf.sub.defn, zf.elem_sep],
)


@Theorem(ForAll(y, bigunion(sing(y)) == y))
def bigunion_sing(l):
    y = l.fix()
    l.rw(zf.ext_ax)
    l.fix()
    l.rw(zf.bigunion_ax)
    # The only member of {y} is y itself.
    l.split()
    l.intro()
    (w, _) = l.obtain(-1)
    l.auto(by=[zf.elem_sing(w, y)])
    l.intro()
    l.exists(y)
    l.auto(by=[zf.elem_sing(y, y)])


pair_elem_prod = prove(
    ForAll([x, y, A, B], elem(pair(x, y), prod(A, B)) == And(elem(x, A), elem(y, B))),
    by=[elem_prod_strong, zf.pair_inj],
)


@Theorem(ForAll([x, y, f], elem(pair(x, y), f), elem(y, ran(f))))
def elem_ran_of_pair_elem(l):
    x, y, f = l.fixes()
    l.intro()
    l.unfold(ran)
    l.rw(zf.elem_sep)
    # y ∈ {x, y} ∈ (x, y) ∈ f, so y ∈ ⋃⋃f.
    l.have(elem(upair(x, y), bigunion(f)), by=[zf.bigunion_ax, zf.elem_pair])
    l.auto(by=[zf.bigunion_ax, zf.elem_upair])


# Functions

is_func = define(
    "is_func",
    [f, X, Y],
    And(
        f <= prod(X, Y),
        ForAll(x, elem(x, X), Exists(y, elem(pair(x, y), f))),
        ForAll([x, y, z], elem(pair(x, y), f), elem(pair(x, z), f), y == z),
    ),
)

app = define("app", [f, x], bigunion(sep(ran(f), Lambda(y, elem(pair(x, y), f)))))


@Theorem(ForAll([f, X, Y, x, y], is_func(f, X, Y), elem(pair(x, y), f), app(f, x) == y))
def app_eq_of_pair_elem(l):
    f, X, Y, x, y = l.fixes()
    l.intros()
    l.unfold(app)
    # The only value at x is y, so the set of values is {y}.
    l.have(sep(ran(f), Lambda(z, elem(pair(x, z), f))) == sing(y))
    l.rw(zf.ext_ax)
    l.fix()
    l.rw(zf.elem_sep).rw(zf.elem_sing)
    l.auto(by=[is_func.defn(f, X, Y), elem_ran_of_pair_elem(x, y, f)])
    l.auto(by=[bigunion_sing(y)])


@Theorem(
    ForAll([f, X, Y, x], is_func(f, X, Y), elem(x, X), elem(pair(x, app(f, x)), f))
)
def pair_app_elem(l):
    f, X, Y, x = l.fixes()
    l.intros()
    l.have(Exists(y, elem(pair(x, y), f)), by=[is_func.defn(f, X, Y)])
    v, _ = l.obtain(-1)
    l.auto(by=[app_eq_of_pair_elem(f, X, Y, x, v)])


app_elem = prove(
    ForAll([f, X, Y, x], is_func(f, X, Y), elem(x, X), elem(app(f, x), Y)),
    by=[pair_app_elem, is_func.defn, le.defn, pair_elem_prod],
)
