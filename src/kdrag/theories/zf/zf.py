"""
ZF style set theory

- https://en.wikipedia.org/wiki/Zermelo%E2%80%93Fraenkel_set_theory
- Naive Set Theory by Paul Halmos
- https://www.isa-afp.org/entries/ZFC_in_HOL.html

There are multiple specific ways to go about roughly the same thing.

Some versions, such as in Suppes' text have a predicate `is_set` to distinguish
sets from classes. This is not done here.

"""

import kdrag as kd
import kdrag.smt as smt
import functools

ZFSet = smt.DeclareSort("ZFSet")
Set = ZFSet
A, B, x, y, z = smt.Consts("A B x y z", ZFSet)
a, b, c, d, p = kd.FreshVars("a b c d p", ZFSet)

Class = ZFSet >> smt.BoolSort()
P, Q = smt.Consts("P Q", Class)

elem = smt.Function("∈", ZFSet, ZFSet, smt.BoolSort())
elts = kd.define("elts", [A], smt.Lambda([x], elem(x, A)))

zf_db = []

kd.notation.getitem.register(ZFSet, lambda A, x: elem(x, A))

reflects = kd.define("reflects", [P, A], smt.ForAll([x], elem(x, A) == P[x]))
is_set = kd.define("is_set", [P], smt.Exists([A], reflects(P, A)))


# general comprehension is not true. This is Russell's paradox.
@kd.Theorem(smt.Not(smt.ForAll([P], is_set(P))))
def russell(l):
    l.unfold(is_set).unfold(reflects)
    l.assumes(smt.ForAll([P], smt.Exists([A], smt.ForAll([x], elem(x, A) == P[x]))))
    Q = smt.Lambda([x], smt.Not(elem(x, x)))
    l.have(smt.Exists([A], smt.ForAll([x], elem(x, A) == Q[x]))).specialize(0, Q).auto()
    A1 = l.obtain(-1)
    l.have(elem(A1, A1) == Q(A1)).specialize(-1, A1).auto()
    l.show(smt.BoolVal(False), by=[])


def slemma(thm, by=[], **kwargs):
    return kd.prove(thm, by=by + zf_db, **kwargs)


ext_ax = kd.axiom(
    kd.QForAll([A, B], smt.Eq((A == B), smt.ForAll([x], elem(x, A) == elem(x, B))))
)

le = kd.notation.le.define([A, B], kd.QForAll([x], elem(x, A), elem(x, B)))

emp = smt.Const("∅", ZFSet)
elem_emp = kd.axiom(smt.ForAll([x], elem(x, emp) == smt.BoolVal(False)))


# l = kd.Lemma(smt.ForAll([A], (A == emp) == smt.Not(smt.Exists([x], elem(x, A)))))
@kd.tactics.Theorem(smt.ForAll([A], (A == emp) == smt.Not(smt.Exists([x], elem(x, A)))))
def emp_exists_elem(l):
    _A = l.fix()
    l.split()
    with l.sub() as l1:
        l1.intros()
        l1.intros()
        _x = l1.obtain(-1)
        l1.show(smt.BoolVal(False), by=[ext_ax, elem_emp])
    with l.sub() as l2:
        l2.intros()
        l2.rw(ext_ax)
        _x = l2.fix()
        l2.apply(0)
        l2.exists(_x)
        l2.have(elem(_x, emp) == smt.BoolVal(False), by=[elem_emp(_x)])
        l2.have(elem(_x, _A), by=[])

        l2.auto()


# emp_exists_elem = l.qed()


l = kd.Lemma(smt.ForAll([A], smt.Implies((A != emp), smt.Exists([x], elem(x, A)))))
_A = l.fix()
l.auto(by=[emp_exists_elem(_A)])
l.qed()
not_emp_exists_elem = l.qed()

pf1 = kd.prove(
    smt.Exists([x], smt.Implies(a != emp, elem(x, a))), by=[emp_exists_elem(a)]
)
(skolem,), elem_pick0 = kd.tactics.skolem(pf1)
# Note that pick(emp) is undefined. You will not be able to prove anything about it.
pick = kd.define("pick", [a], skolem)


elem_pick = kd.prove(
    smt.Implies(a != emp, elem(pick(a), a)), unfold=1, by=[elem_pick0]
).forall([a])


upair = smt.Function("upair", ZFSet, ZFSet, ZFSet)
elem_upair = kd.axiom(
    kd.QForAll([x, y, z], elem(z, upair(x, y)) == smt.Or(z == x, z == y))
)

l = kd.Lemma(smt.ForAll([a, b], smt.Not(upair(a, b) == emp)))
_a, _b = l.fixes()
l.rw(ext_ax)
l.intros()
l.have(elem(_a, upair(_a, _b)), by=[elem_upair(_a, _b, _a)])
l.have(smt.Not(elem(_a, emp)), by=[elem_emp(_a)])
l.auto()
upair_not_emp = l.qed()

l = kd.Lemma(smt.ForAll([a, b], upair(a, b) == upair(b, a)))
l.fixes()
l.rw(ext_ax)
l.fix()
l.rw(elem_upair)
l.rw(elem_upair)
l.auto()
upair_comm = l.qed()

elem_upair_1 = kd.prove(
    smt.ForAll([a, b], elem(a, upair(a, b)) == smt.BoolVal(True)), by=[elem_upair]
)
elem_upair_2 = kd.prove(
    smt.ForAll([a, b], elem(b, upair(a, b)) == smt.BoolVal(True)), by=[elem_upair]
)


@kd.tactics.Theorem(
    smt.ForAll(
        [a, b, c, d],
        (upair(a, b) == upair(c, d))
        == smt.Or(smt.And(a == c, b == d), smt.And(a == d, b == c)),
    )
)
def upair_inj(l):
    a, b, c, d = l.fixes()
    l.split()
    l.intros()
    l.rw(ext_ax, at=0)
    l.have(elem(a, upair(a, b)), by=elem_upair_1)
    l.have(elem(b, upair(a, b)), by=elem_upair_2)
    l.have(elem(c, upair(c, d)), by=elem_upair_1)
    l.have(elem(d, upair(c, d)), by=elem_upair_2)
    l.auto(by=[elem_upair])
    l.intros()
    l.auto(by=[upair_comm])


pick_upair = kd.prove(
    smt.ForAll([a, b], smt.Or(pick(upair(a, b)) == a, pick(upair(a, b)) == b)),
    by=[elem_pick, elem_upair, elem_emp],
)


sing = kd.define("sing", [x], upair(x, x))


def FinSet(*xs):
    """
    A helper for sets of the form {x1, x2, ..., xn}
    """
    return functools.reduce(lambda a, b: sing(b) | a, xs, emp)


@kd.tactics.Theorem(smt.ForAll([a, b], elem(a, sing(b)) == (a == b)))
def elem_sing(l):
    a, b = l.fixes()
    l.unfold(sing)
    l.auto(by=[elem_upair])


sing_not_emp = kd.prove(smt.Not(sing(a) == emp), unfold=1, by=[upair_not_emp]).forall(
    [a]
)


@kd.tactics.Theorem(smt.ForAll([a], pick(sing(a)) == a))
def pick_sing(l):
    _a = l.fix()
    l.unfold(sing)
    l.auto(by=[pick_upair])
    # l.rw(ext_ax)
    # _x = l.fix()
    # l.auto(by=[elem_sing, elem_pick, elem_emp])


# Separation

sep = smt.Function("sep", ZFSet, Class, ZFSet)
elem_sep = kd.axiom(
    kd.QForAll([P, A, x], elem(x, sep(A, P)) == smt.And(P[x], elem(x, A)))
)


@kd.Theorem(
    kd.QForAll(
        [a, b, P],
        sep(upair(a, b), P)
        == smt.If(P(a), smt.If(P(b), upair(a, b), sing(a)), smt.If(P(b), sing(b), emp)),
    )
)
def sep_upair(l):
    a, b, P = l.fixes()
    l.rw(ext_ax)
    l.fix()
    l.rw(elem_sep)
    l.cases(P(a))
    l.rw(-1)
    l.cases(P(b))
    l.rw(-1)
    l.simp()
    l.auto(by=[elem_upair])
    l.rw(-1)
    l.simp()
    l.auto(by=[elem_upair, elem_sing])
    l.rw(-1)
    l.cases(P(b))
    l.rw(-1)
    l.auto(by=[elem_upair, elem_sing])
    l.rw(-1)
    l.simp()
    l.auto(by=[elem_emp, elem_upair])


zf_db.extend([elem_emp, elem_upair, ext_ax, elem_sep])

# bigunion

bigunion = smt.Function("bigunion", ZFSet, ZFSet)  # ⋃
bigunion_ax = kd.axiom(
    kd.QForAll(
        [A, x], smt.Eq(elem(x, bigunion(A)), kd.QExists([B], elem(B, A), elem(x, B)))
    )
)


# Binary Union

union = kd.define("union", [A, B], bigunion(upair(A, B)))
kd.notation.or_.register(Set, union)

l = kd.Lemma(a | b == b | a)
l.unfold(union)
l.rw(ext_ax)
_x = l.fix()
l.auto(by=[elem_upair, bigunion_ax])
union_comm = l.qed().forall([a, b])

l = kd.Lemma(
    smt.ForAll([x, A, B], elem(x, bigunion(upair(A, B))) == (elem(x, A) | elem(x, B)))
)
_x, _A, _B = l.fixes()
l.rw(bigunion_ax)
l.split()
with l.sub() as c1:
    c1.intros()
    _B1 = c1.obtain(0)
    c1.rw(elem_upair, at=0)
    c1.auto()
with l.sub() as c2:
    c2.intros()
    c2.cases(elem(_x, _A))
    c2.exists(_A)
    c2.rw(elem_upair)
    c2.auto()

    c2.exists(_B)
    c2.rw(elem_upair)
    c2.auto()
elem_bigunion_upair = l.qed()


l = kd.Lemma(smt.ForAll([x, A, B], elem(x, A | B) == (elem(x, A) | elem(x, B))))
_x, _A, _B = l.fixes()
l.unfold(union)
l.rw(elem_bigunion_upair)
l.auto()
elem_union = l.qed()


l = kd.Lemma(smt.ForAll([a, b, c], (a | b) | c == a | (b | c)))
_a, _b, _c = l.fixes()
l.rw(ext_ax)
_x = l.fix()
l.rw(elem_union)
l.rw(elem_union)
l.rw(elem_union)
l.rw(elem_union)
l.auto()
union_assoc = l.qed()

l = kd.Lemma(smt.ForAll([a], a | a == a))
l.fixes()
l.rw(ext_ax)
l.fix()
l.rw(elem_union)
l.auto()
union_idem = l.qed()

l = kd.Lemma(smt.ForAll([a, b, c], a <= a | b))
l.fixes()
l.unfold(le)
l.fix()
l.rw(elem_union)
l.auto()
le_union = l.qed()


@kd.tactics.Theorem(smt.ForAll([a, b], sing(a) | upair(a, b) == upair(a, b)))
def sing_union_upair(l):
    a, b = l.fixes()
    l.rw(ext_ax)
    l.fix()
    l.rw(elem_union)
    l.rw(elem_upair)
    l.rw(elem_sing)
    l.auto()


@kd.tactics.Theorem(smt.ForAll([a, b], bigunion(upair(a, b)) == a | b))
def bigunion_upair(l):
    a, b = l.fixes()
    l.rw(ext_ax)
    _ = l.fix()
    l.rw(elem_bigunion_upair)
    l.rw(elem_union)
    l.auto()


# Biginter
biginter = kd.define(
    "biginter",
    [a],
    sep(pick(a), smt.Lambda([x], kd.QForAll([b], elem(b, a), elem(x, b)))),
)
# huh. biginter(emp) is undefined since we can't pick from it.
l = kd.Lemma(
    smt.ForAll(
        [A, x],
        smt.Implies(
            A != emp, elem(x, biginter(A)) == kd.QForAll([b], elem(b, A), elem(x, b))
        ),
    )
)
_A, _x = l.fixes()
l.intros()
l.unfold(biginter)
l.rw(elem_sep)
l.simp()
l.split()
l.intros()
l.split()
l.auto()
l.have(elem(pick(_A), _A), by=[elem_pick])
l.auto()

l.intros()
_b = l.fix()
l.intros()
l.have(elem(pick(_A), _A), by=[elem_pick])
l.auto()
elem_biginter = l.qed()


# Intersection

inter = kd.define("inter", [A, B], sep(A, smt.Lambda([x], elem(x, B))))
kd.notation.and_.register(Set, inter)

l = kd.Lemma(smt.ForAll([x, A, B], elem(x, A & B) == (elem(x, A) & elem(x, B))))
l.fixes()
l.unfold(inter)
l.rw(elem_sep)
l.auto()
elem_inter = l.qed()

l = kd.Lemma(smt.ForAll([A, B], biginter(upair(A, B)) == inter(A, B)))
_A, _B = l.fixes()
l.rw(ext_ax)
l.have(upair(_A, _B) != emp, by=[upair_not_emp(_A, _B)])
_x = l.fix()
l.rw(elem_inter)
l.auto(by=[elem_biginter, elem_upair])
biginter_upair_inter = l.qed()

l = kd.Lemma(smt.ForAll([A, B], A & B == B & A))
l.fixes()
l.rw(ext_ax)
l.fix()
l.rw(elem_inter)
l.rw(elem_inter)
l.auto()
inter_comm = l.qed()

l = kd.Lemma(smt.ForAll([a, b, c], (a & b) & c == a & (b & c)))
l.fixes()
l.rw(ext_ax)
l.fix()
l.rw(elem_inter)
l.rw(elem_inter)
l.rw(elem_inter)
l.rw(elem_inter)
l.auto()
inter_assoc = l.qed()


l = kd.Lemma(smt.ForAll([a], a & a == a))
l.fixes()
l.rw(ext_ax)
l.fix()
l.rw(elem_inter)
l.auto()
inter_idem = l.qed()


l = kd.Lemma(smt.ForAll([a, b, c], a & (b | c) == (a & b) | (a & c)))
l.fixes()
l.rw(ext_ax)
l.fix()
l.rw(elem_inter)
l.rw(elem_union)
l.rw(elem_inter)
l.rw(elem_union)
l.rw(elem_inter)
l.auto()
inter_union_distr = l.qed()

l = kd.Lemma(smt.ForAll([a, b], a & b <= a))
l.fixes()
l.unfold(le)
l.fix()
l.rw(elem_inter)
l.auto()
inter_le = l.qed()


@kd.Theorem(smt.ForAll([a, b, x], (x <= (a & b)) == ((x <= a) & (x <= b))))
def le_inter_2(l):
    a, b, x = l.fixes()
    l.unfold(le)
    l.split()
    l.auto(by=[elem_inter])
    l.auto(by=[elem_inter])


l = kd.Lemma(smt.ForAll([x], x & emp == emp))
l.fixes()
l.rw(ext_ax)
l.fix()
l.rw(elem_inter)
l.rw(elem_emp)
l.auto()
inter_emp = l.qed()


l = kd.Lemma(smt.ForAll([a, b, c], (a | b) & c == (a & c) | (b & c)))
l.fixes()
l.auto(by=[inter_comm, inter_union_distr])
union_inter_distr = l.qed()


@kd.tactics.Theorem(
    smt.ForAll(
        [a, b, c],
        inter(a, upair(b, c))
        == smt.If(
            elem(b, a),
            smt.If(elem(c, a), upair(b, c), sing(b)),
            smt.If(elem(c, a), sing(c), emp),
        ),
    )
)
def inter_upair_2(l):
    a, b, c = l.fixes()
    l.unfold(inter)
    l.rw(ext_ax)
    _x = l.fix()
    l.rw(elem_sep)
    l.simp()
    l.rw(elem_upair)
    l.cases(elem(b, a))
    l.rw(-1)
    l.cases(elem(c, a))

    l.rw(-1)
    l.simp()
    l.rw(elem_upair)
    l.auto()

    l.rw(-1)
    l.simp()
    l.rw(elem_sing)
    l.auto()

    l.rw(-1)
    l.cases(elem(c, a))
    l.rw(-1)
    l.simp()
    l.rw(elem_sing)
    l.auto()

    l.rw(-1)
    l.simp()
    l.auto(by=[elem_emp])


inter_upair_1 = kd.prove(
    smt.ForAll(
        [a, b, c],
        inter(upair(b, c), a)
        == smt.If(
            elem(b, a),
            smt.If(elem(c, a), upair(b, c), sing(b)),
            smt.If(elem(c, a), sing(c), emp),
        ),
    ),
    by=[inter_upair_2, inter_comm],
)

# Difference

sub = kd.notation.sub.define([A, B], sep(A, smt.Lambda([x], smt.Not(elem(x, B)))))


@kd.Theorem(kd.QForAll([a, b], upair(a, b) - sing(a) == smt.If(a == b, emp, sing(b))))
def upair_sub_sing(l):
    a, b = l.fixes()
    l.unfold(sub)
    l.rw(sep_upair)
    l.simp()
    l.rw(elem_sing)
    l.rw(elem_sing)
    l.simp()
    l.auto()


# Power

pow = smt.Function("pow", ZFSet, ZFSet)
elem_pow = kd.axiom(smt.ForAll([A, x], elem(x, pow(A)) == (x <= A)))


@kd.Theorem(smt.ForAll([a, b], pow(a & b) == pow(a) & pow(b)))
def pow_inter(l):
    a, b = l.fixes()
    l.rw(ext_ax).fix()
    l.rw(elem_inter).rw(elem_pow).rw(elem_pow).rw(elem_pow).rw(le_inter_2)
    l.auto()


# Ordered Pair


pair = kd.define("pair", [a, b], upair(sing(a), upair(a, b)))
is_pair = kd.define("is_pair", [c], smt.Exists([a, b], pair(a, b) == c))
fst = kd.define("fst", [p], pick(biginter(p)))
snd = kd.define(
    "snd",
    [p],
    smt.If(sing(sing(fst(p))) == p, fst(p), pick(bigunion(p) - sing(fst(p)))),
)


@kd.Theorem(smt.ForAll([a, b], is_pair(pair(a, b)) == smt.BoolVal(True)))
def is_pair_pair(l):
    a, b = l.fixes()
    l.unfold(is_pair)
    l.auto()


@kd.tactics.Theorem(
    smt.ForAll([a, b, c, d], (pair(a, b) == pair(c, d)) == smt.And(a == c, b == d))
)
def pair_inj(l):
    a, b, c, d = l.fixes()
    l.unfold(pair)
    l.unfold(sing)
    l.split()
    l.intros()
    l.rw(upair_inj, at=0)
    l.auto(by=[upair_inj])
    l.intros()
    l.auto(by=[upair_comm])


@kd.tactics.Theorem(smt.ForAll([a, b], fst(pair(a, b)) == a))
def fst_pair(l):
    a, b = l.fixes()
    l.unfold(fst)
    l.unfold(pair)
    l.rw(biginter_upair_inter)
    l.rw(inter_upair_2)
    l.rw(elem_sing)
    l.rw(elem_sing)
    l.simp()
    l.cases(b == a)

    # case a == b
    l.rw(-1)
    l.simp()
    l.auto(by=[pick_upair])

    # case a != b
    l.rw(-1)
    l.simp()
    l.auto(by=[pick_sing])


@kd.tactics.Theorem(smt.ForAll([a, b], snd(pair(a, b)) == b))
def snd_pair(l):
    a, b = l.fixes()
    l.unfold(snd)
    l.rw(fst_pair)
    l.cases(sing(sing(a)) == pair(a, b))

    l.rw(-1)
    l.simp()
    l.unfold(sing, at=0)
    l.unfold(pair, at=0)
    l.unfold(sing, at=0)
    l.auto(by=[upair_inj])

    l.rw(-1)
    l.simp()
    l.unfold(pair)
    l.rw(bigunion_upair)
    l.rw(sing_union_upair)
    l.rw(upair_sub_sing)
    l.have((a == b) == smt.BoolVal(False))
    l.unfold(pair, at=0)
    l.unfold(sing, at=0)
    l.auto(by=[upair_inj])
    l.rw(-1)
    l.simp()
    l.rw(pick_sing)
    l.auto()


@kd.tactics.Theorem(
    smt.ForAll([a, b, x], elem(x, pair(a, b)) == smt.Or(x == sing(a), x == upair(a, b)))
)
def elem_pair(l):
    a, b, c = l.fixes()
    l.unfold(pair)
    l.rw(elem_upair)
    l.auto()


def test():
    """
    >>> True
    True
    """
