"""
Functions as sets of ordered pairs (Halmos §8), and HOL functions between sets.

A function is its graph. `app(f, x)` reads the value at `x` without choice,
as `⋃{y | (x, y) ∈ f}` (Isabelle/ZF's `apply`); off the domain it is junk.
"""

from kdrag import Theorem, define, prove
from kdrag.smt import (
    And,
    ArraySort,
    Consts,
    Exists,
    ForAll,
    Lambda,
    Not,
)
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import (
    ZFSet,
    bigunion,
    elem,
    le,
    pair,
    pow,
    prod,
    ran,
    sep,
    sing,
    upair,
)

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


@Theorem(
    ForAll([x, y, A, B], elem(pair(x, y), prod(A, B)) == And(elem(x, A), elem(y, B)))
)
def pair_elem_prod(l):
    x, y, A, B = l.fixes()
    l.rw(zf.elem_prod_def)
    l.split()
    # → : (x, y) = (x', y') with x' ∈ A, y' ∈ B, and pairs are injective.
    l.intro()
    l.auto(by=[zf.pair_inj])
    # ← : {x} and {x, y} are subsets of A ∪ B.
    l.intro()
    l.have(sing(x) <= A | B, by=[le.defn, zf.elem_sing, zf.elem_union])
    l.have(upair(x, y) <= A | B, by=[le.defn, zf.elem_upair, zf.elem_union])
    l.have(
        elem(pair(x, y), pow(pow(A | B))),
        by=[zf.elem_pow, le.defn, zf.elem_pair],
    )
    l.auto()


# Choice-free intersection, as in Mathlib's ZFSet.sInter. The intersection in
# theories.zf separates from `pick(a)`, which uses global choice.
sinter = define(
    "sinter", [A], sep(bigunion(A), Lambda(x, ForAll(B, elem(B, A), elem(x, B))))
)


@Theorem(
    ForAll(
        [A, x],
        A != zf.emp,
        elem(x, sinter(A)) == ForAll(B, elem(B, A), elem(x, B)),
    )
)
def elem_sinter(l):
    A, x = l.fixes()
    l.intro()
    l.unfold(sinter)
    l.rw(zf.elem_sep)
    # x in every member of a nonempty A is in some member, so x ∈ ⋃A.
    l.have(Exists(B, elem(B, A)), by=[zf.not_emp_exists_elem(A)])
    l.auto(by=[zf.bigunion_ax(A, x)])


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


# Choice-free coordinates of an ordered pair (Kuratowski): ⋂(x, y) = {x}, so
# ⋃⋂(x, y) = x. The fst/snd of theories.zf go through `pick`.
pfst = define("pfst", [x], bigunion(sinter(x)))


@Theorem(ForAll([x, y], pfst(pair(x, y)) == x))
def pfst_pair(l):
    x, y = l.fixes()
    l.unfold(pfst)
    # ⋂{{x}, {x, y}} = {x}
    l.have(sinter(pair(x, y)) == sing(x))
    l.rw(zf.ext_ax)
    z0 = l.fix()
    # {x} ∈ (x, y), so the pair is nonempty and its members are {x} and {x, y}.
    l.have(elem(sing(x), pair(x, y)), by=[zf.elem_pair(x, y, sing(x))])
    l.have(pair(x, y) != zf.emp, by=[zf.elem_emp(sing(x))])
    l.have(
        elem(z0, sinter(pair(x, y))) == And(elem(z0, sing(x)), elem(z0, upair(x, y))),
        by=[elem_sinter(pair(x, y), z0), zf.elem_pair, zf.elem_upair(x, y, x)],
    )
    # z is in both {x} and {x, y} iff z = x.
    l.auto(by=[zf.elem_sing(z0, x), zf.elem_upair(x, y, z0)])
    l.auto(by=[bigunion_sing(x)])


# The second coordinate: the unique y ∈ ⋃p with p = (pfst p, y).
psnd = define("psnd", [x], bigunion(sep(bigunion(x), Lambda(y, x == pair(pfst(x), y)))))


@Theorem(ForAll([x, y], psnd(pair(x, y)) == y))
def psnd_pair(l):
    x, y = l.fixes()
    l.unfold(psnd)
    # {z ∈ ⋃(x, y) | (x, y) = (pfst (x, y), z)} = {y}, as pfst (x, y) = x.
    p = pair(x, y)
    l.have(sep(bigunion(p), Lambda(z, p == pair(pfst(p), z))) == sing(y))
    l.rw(zf.ext_ax)
    z0 = l.fix()
    l.rw(zf.elem_sep)
    l.simp()
    l.have(pfst(p) == x, by=[pfst_pair])
    l.have(
        elem(y, bigunion(p)),
        by=[
            zf.bigunion_ax(p, y),
            zf.elem_pair(x, y, upair(x, y)),
            zf.elem_upair(x, y, y),
        ],
    )
    l.auto(by=[zf.pair_inj, zf.elem_sing(z0, y)])
    l.auto(by=[bigunion_sing(y)])
