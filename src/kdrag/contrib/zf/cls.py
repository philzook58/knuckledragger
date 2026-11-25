"""
Classes and the sets that reflect them.

A class is a predicate `ZFSet → Bool` (`zf.Class`); z3 compares classes
extensionally on its own. `zf.reflects(C, A)` says the set A has exactly the
members of C, like `has_lim` for limits: a relation, not a total function, so
no junk values. `zf.is_set(C)` says some set reflects C.

The set operations then have class versions, and each ZF axiom becomes a
smallness statement: the class built from small classes is small. These are
proved here from the existing axioms, so this module adds no axioms. Russell's
paradox and Burali-Forti become statements that some classes are not sets.
"""

import kdrag as kd
from kdrag import Theorem, define, define_const
from kdrag.smt import And, ArraySort, BoolVal, Consts, Exists, ForAll, Lambda, Not, Or
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

A, B, a, b, x, y, z = Consts("A B a b x y z", ZFSet)
C, D = Consts("C D", Class)
F = Consts("F", ArraySort(ZFSet, ZFSet))[0]

# A set reflects at most one class, and a class is reflected by at most one set.
reflects_unique = kd.prove(
    ForAll([C, A, B], reflects(C, A), reflects(C, B), A == B),
    by=[reflects.defn, zf.ext_ax],
)

# The class operations, as in Mathlib's `Class`. Each is named, so z3 sees a
# constant rather than a lambda (see #106).
set_cls = define("set_cls", [A], Lambda(x, elem(x, A)))  # A as a class
univ = define_const("univ", Lambda(x, BoolVal(True)))
cempty = define_const("cempty", Lambda(x, BoolVal(False)))
cpair = define("cpair", [a, b], Lambda(x, Or(x == a, x == b)))
cinter = define("cinter", [C, D], Lambda(x, And(C[x], D[x])))
csUnion = define("csUnion", [C], Lambda(x, Exists(y, And(C[y], elem(x, y)))))
cpowerset = define("cpowerset", [C], Lambda(x, ForAll(y, elem(y, x), C[y])))
cimage = define("cimage", [F, C], Lambda(y, Exists(x, And(C[x], F[x] == y))))


@Theorem(ForAll(A, reflects(set_cls(A), A)))
def reflects_set_cls(l):
    l.fix()
    l.unfold(reflects)
    l.auto(by=[set_cls.defn])


# The ZF axioms as smallness of classes.


@Theorem(is_set(cempty))
def is_set_empty(l):
    l.unfold(is_set)
    l.exists(emp)
    l.auto(by=[reflects.defn, cempty.defn, zf.elem_emp])


@Theorem(ForAll([a, b], is_set(cpair(a, b))))
def is_set_pair(l):
    a, b = l.fixes()
    l.unfold(is_set)
    l.exists(upair(a, b))
    l.auto(by=[reflects.defn, cpair.defn, zf.elem_upair])


@Theorem(ForAll([C, D], is_set(D), is_set(cinter(C, D))))
def is_set_inter(l):
    """Separation: a subclass of a set is a set."""
    C, D = l.fixes()
    l.intro()
    l.unfold(is_set, at=0)
    A0 = l.obtain(0)[0]
    l.unfold(is_set)
    l.exists(sep(A0, C))
    l.auto(by=[reflects.defn, cinter.defn, zf.elem_sep])


@Theorem(ForAll(C, is_set(C), is_set(csUnion(C))))
def is_set_sUnion(l):
    """Union: the union of a set of sets is a set."""
    l.fix()
    l.intro()
    l.unfold(is_set, at=0)
    A0 = l.obtain(0)[0]
    l.unfold(is_set)
    l.exists(bigunion(A0))
    l.auto(by=[reflects.defn, csUnion.defn, zf.bigunion_ax])


@Theorem(ForAll(C, is_set(C), is_set(cpowerset(C))))
def is_set_powerset(l):
    """Power set: the subsets of a set form a set."""
    l.fix()
    l.intro()
    l.unfold(is_set, at=0)
    A0 = l.obtain(0)[0]
    l.unfold(is_set)
    l.exists(pow(A0))
    l.auto(by=[reflects.defn, cpowerset.defn, zf.elem_pow, zf.le.defn])


@Theorem(ForAll([F, C], is_set(C), is_set(cimage(F, C))))
def is_set_image(l):
    """Replacement: the image of a set is a set."""
    F, C = l.fixes()
    l.intro()
    l.unfold(is_set, at=0)
    A0 = l.obtain(0)[0]
    l.unfold(is_set)
    l.exists(repl(F, A0))
    l.auto(by=[reflects.defn, cimage.defn, elem_repl])


@Theorem(is_set(Lambda(x, ForAll(A, is_inductive(A), elem(x, A)))))
def is_set_omega(l):
    """Infinity: the class of natural numbers is a set, namely ω."""
    l.unfold(is_set)
    l.exists(omega)
    l.auto(by=[reflects.defn, elem_omega])


# Classes that are not sets.


@Theorem(Not(is_set(Lambda(x, Not(elem(x, x))))))
def not_is_set_russell(l):
    """Russell: the class of sets that are not members of themselves."""
    l.intro()
    l.unfold(is_set, at=0)
    A0 = l.obtain(0)[0]
    l.auto(by=[reflects.defn(Lambda(x, Not(elem(x, x))), A0)])


@Theorem(Not(is_set(univ)))
def not_is_set_univ(l):
    """The universe is not a set, or by separation Russell's class would be."""
    l.intro()
    l.have(is_set(cinter(Lambda(x, Not(elem(x, x))), univ)), by=[is_set_inter])
    l.have(
        cinter(Lambda(x, Not(elem(x, x))), univ) == Lambda(x, Not(elem(x, x))),
        by=[cinter.defn, univ.defn],
    )
    l.auto(by=[not_is_set_russell])


Ord = define_const("Ord", Lambda(x, is_ordinal(x)))


@Theorem(Not(is_set(Ord)))
def not_is_set_ord(l):
    """Burali-Forti: the ordinals do not form a set."""
    l.intro()
    l.unfold(is_set, at=0)
    A0 = l.obtain(0)[0]
    l.have(ForAll(A, is_ordinal(A), elem(A, A0)), by=[reflects.defn, Ord.defn])
    l.auto(by=[burali_forti])
