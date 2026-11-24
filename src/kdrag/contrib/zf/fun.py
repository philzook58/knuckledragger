"""
Functions as sets of ordered pairs (Halmos §8), and HOL functions between sets.

A function is its graph. `app(f, x)` reads the value at `x` without choice,
as `⋃{y | (x, y) ∈ f}` (Isabelle/ZF's `apply`); off the domain it is junk.
"""

import kdrag as kd
from kdrag import FreshVar, Theorem, define, prove
from kdrag.smt import (
    And,
    ArraySort,
    BoolSort,
    Consts,
    Exists,
    ForAll,
    Lambda,
    Not,
    substitute,
)
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
F = Consts("F", ArraySort(ZFSet, ZFSet))[0]

# Small set facts missing from theories.zf

elem_sub = prove(
    ForAll([x, A, B], elem(x, A - B) == And(elem(x, A), Not(elem(x, B)))),
    by=[zf.sub.defn, zf.elem_sep],
)


@Theorem(ForAll(y, bigunion(sing(y)) == y))
def bigunion_sing(l):
    y = l.fix()
    l.rw(zf.ext_ax)
    z = l.fix()
    # z ∈ ⋃{y} means z ∈ B for some B ∈ {y}, and the only such B is y.
    l.auto(by=[zf.bigunion_ax(sing(y), z), zf.elem_sing])


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


# HOL functions between sets, as in Mathlib's Set.MapsTo, InjOn, SurjOn, BijOn.
# A one-to-one correspondence (Halmos §8, §13) is `bij_on(F, A, B)`.

maps_to = define("maps_to", [F, A, B], ForAll(x, elem(x, A), elem(F[x], B)))
inj_on = define(
    "inj_on", [F, A], ForAll([x, y], elem(x, A), elem(y, A), F[x] == F[y], x == y)
)
surj_on = define(
    "surj_on",
    [F, A, B],
    ForAll(y, elem(y, B), Exists(x, And(elem(x, A), F[x] == y))),
)
bij_on = define(
    "bij_on", [F, A, B], And(maps_to(F, A, B), inj_on(F, A), surj_on(F, A, B))
)


# Choice of a function: global choice is built into kd via `obtain`.
R = Consts("R", ArraySort(ZFSet, ZFSet, BoolSort()))[0]
_R, _x = FreshVar("R", R.sort()), FreshVar("x", ZFSet)
assert isinstance(_R, kd.smt.ArrayRef)
(_choice,), _choice_spec = kd.kernel.obtain(Exists(y, _R[_x, y]))


@Theorem(ForAll(R, ForAll(x, Exists(y, R[x, y])), Exists(F, ForAll(x, R[x, F[x]]))))
def exists_choice_fn(l):
    R = l.fix()
    l.intro()
    l.exists(Lambda(_x, substitute(_choice, (_R, R))))
    z = l.fix()
    l.auto(by=[_choice_spec.forall([_R, _x])(R, z)])
