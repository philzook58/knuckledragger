"""
Classes and the sets whose members they are.

A class is a predicate `ZFSet → Bool` (`zf.Class`), and z3 compares classes
extensionally on its own. `elts(x)` is the class of members of x, as in
Isabelle's ZFC_in_HOL (Mathlib's coercion `↑x`). "x has exactly the members of
C" is then the equation `elts(x) == C`, and C is a set when some x solves it
(`is_set_iff`, bridging to `zf.is_set`). Like `has_lim`, this is a relation
rather than a total function, so there are no junk values.

Each set operation commutes with `elts` (`elts_sep`, `elts_bigunion`, ...), as
in Mathlib's `ZFSet.coe_sep`. The ZF axioms then become smallness statements:
the class built from small classes is small. These are proved from the existing
axioms, so this module adds none. Russell's paradox and Burali-Forti say that
some classes are not sets.
"""

from kdrag import Theorem, define, define_const
from kdrag.smt import And, ArraySort, BoolVal, Consts, Eq, Exists, ForAll, Lambda, Not, Or
import kdrag.theories.zf.zf as zf
from kdrag.theories.zf.zf import (
    Class,
    ZFSet,
    bigunion,
    elem,
    emp,
    is_set,
    pow,
    reflects,
    sep,
    upair,
)
from kdrag.contrib.zf.nat import elem_omega, is_inductive, omega
from kdrag.contrib.zf.ordinal import elem_repl, is_ordinal, repl
from kdrag.contrib.zf.ordset import burali_forti

A, B, a, b, x, y = Consts("A B a b x y", ZFSet)
C, D = Consts("C D", Class)
F = Consts("F", ArraySort(ZFSet, ZFSet))[0]

# The members of a set, as a class.
elts = define("elts", [A], Lambda(x, elem(x, A)))


@Theorem(ForAll([A, B], elts(A) == elts(B), A == B))
def elts_inj(l):
    """Extensionality: a set is determined by its members."""
    l.fixes()
    l.intro()
    # Equal classes are equal lambdas, which z3 compares pointwise.
    l.unfold(elts, at=0)
    l.rw(zf.ext_ax)
    l.auto()


@Theorem(ForAll([C, A], Eq(reflects(C, A), elts(A) == C)))
def reflects_iff(l):
    C, A = l.fixes()
    l.unfold(reflects)
    l.unfold(elts)
    l.auto()


@Theorem(ForAll(C, Eq(is_set(C), Exists(A, elts(A) == C))))
def is_set_iff(l):
    """Isabelle's small_iff: a class is a set when it is the members of a set."""
    l.fix()
    l.unfold(is_set)
    l.auto(by=[reflects_iff])


# The class operations, as in Mathlib's `ZFClass`. Each is named, so z3 sees a
# constant rather than a lambda (see #106).
univ = define_const("univ", Lambda(x, BoolVal(True)))
cempty = define_const("cempty", Lambda(x, BoolVal(False)))
cpair = define("cpair", [a, b], Lambda(x, Or(x == a, x == b)))
cinter = define("cinter", [C, D], Lambda(x, And(C[x], D[x])))
csUnion = define("csUnion", [C], Lambda(x, Exists(y, And(C[y], elem(x, y)))))
cpowerset = define("cpowerset", [C], Lambda(x, ForAll(y, elem(y, x), C[y])))
cimage = define("cimage", [F, C], Lambda(y, Exists(x, And(C[x], F[x] == y))))


# Each set operation commutes with elts.


@Theorem(elts(emp) == cempty)
def elts_emp(l):
    l.unfold(elts)
    l.unfold(cempty)
    l.auto(by=[zf.elem_emp])


@Theorem(ForAll([a, b], elts(upair(a, b)) == cpair(a, b)))
def elts_upair(l):
    l.fixes()
    l.unfold(elts)
    l.unfold(cpair)
    l.auto(by=[zf.elem_upair])


@Theorem(ForAll([A, C], elts(sep(A, C)) == cinter(C, elts(A))))
def elts_sep(l):
    l.fixes()
    l.unfold(elts)
    l.unfold(cinter)
    l.auto(by=[zf.elem_sep])


@Theorem(ForAll(A, elts(bigunion(A)) == csUnion(elts(A))))
def elts_bigunion(l):
    l.fix()
    l.unfold(elts)
    l.unfold(csUnion)
    l.auto(by=[zf.bigunion_ax])


@Theorem(ForAll(A, elts(pow(A)) == cpowerset(elts(A))))
def elts_pow(l):
    l.fix()
    l.unfold(elts)
    l.unfold(cpowerset)
    l.auto(by=[zf.elem_pow, zf.le.defn])


@Theorem(ForAll([F, A], elts(repl(F, A)) == cimage(F, elts(A))))
def elts_repl(l):
    l.fixes()
    l.unfold(elts)
    l.unfold(cimage)
    l.auto(by=[elem_repl])


@Theorem(elts(omega) == Lambda(x, ForAll(A, is_inductive(A), elem(x, A))))
def elts_omega(l):
    """Infinity: ω is the class of natural numbers."""
    l.unfold(elts)
    l.auto(by=[elem_omega])


# The ZF axioms as smallness of classes, from the equations above.


@Theorem(ForAll([C, D], is_set(D), is_set(cinter(C, D))))
def is_set_inter(l):
    """Separation: a subclass of a set is a set."""
    C, D = l.fixes()
    l.intro()
    l.rw(is_set_iff(D), at=0)
    A0 = l.obtain(0)[0]
    l.rw(is_set_iff(cinter(C, D)))
    l.exists(sep(A0, C))
    l.auto(by=[elts_sep(A0, C)])


@Theorem(ForAll(C, is_set(C), is_set(csUnion(C))))
def is_set_sUnion(l):
    """Union: the union of a set of sets is a set."""
    C = l.fix()
    l.intro()
    l.rw(is_set_iff(C), at=0)
    A0 = l.obtain(0)[0]
    l.rw(is_set_iff(csUnion(C)))
    l.exists(bigunion(A0))
    l.auto(by=[elts_bigunion(A0)])


@Theorem(ForAll(C, is_set(C), is_set(cpowerset(C))))
def is_set_powerset(l):
    """Power set: the subsets of a set form a set."""
    C = l.fix()
    l.intro()
    l.rw(is_set_iff(C), at=0)
    A0 = l.obtain(0)[0]
    l.rw(is_set_iff(cpowerset(C)))
    l.exists(pow(A0))
    l.auto(by=[elts_pow(A0)])


@Theorem(ForAll([F, C], is_set(C), is_set(cimage(F, C))))
def is_set_image(l):
    """Replacement: the image of a set is a set."""
    F, C = l.fixes()
    l.intro()
    l.rw(is_set_iff(C), at=0)
    A0 = l.obtain(0)[0]
    l.rw(is_set_iff(cimage(F, C)))
    l.exists(repl(F, A0))
    l.auto(by=[elts_repl(F, A0)])


# Classes that are not sets.

russell_cls = define_const("russell_cls", Lambda(x, Not(elem(x, x))))


@Theorem(Not(is_set(russell_cls)))
def not_is_set_russell(l):
    """Russell: the sets that are not members of themselves."""
    l.rw(is_set_iff(russell_cls))
    l.intro()
    A0 = l.obtain(0)[0]
    # A0 ∈ A0 holds exactly when it does not.
    l.have(elem(A0, A0) == Not(elem(A0, A0)), by=[elts.defn(A0), russell_cls.defn])
    l.auto()


@Theorem(Not(is_set(univ)))
def not_is_set_univ(l):
    """The universe is not a set, or by separation Russell's class would be."""
    l.intro()
    l.have(is_set(cinter(russell_cls, univ)), by=[is_set_inter])
    l.have(cinter(russell_cls, univ) == russell_cls, by=[cinter.defn, univ.defn])
    l.auto(by=[not_is_set_russell])


Ord = define_const("Ord", Lambda(x, is_ordinal(x)))


@Theorem(Not(is_set(Ord)))
def not_is_set_ord(l):
    """Burali-Forti: the ordinals do not form a set."""
    l.rw(is_set_iff(Ord))
    l.intro()
    A0 = l.obtain(0)[0]
    l.have(ForAll(A, is_ordinal(A), elem(A, A0)), by=[elts.defn(A0), Ord.defn])
    l.auto(by=[burali_forti])
