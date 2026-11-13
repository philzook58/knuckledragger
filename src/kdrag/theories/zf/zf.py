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
from kdrag import FreshVars, Lemma, QExists, QForAll, Theorem, axiom, define, prove
from kdrag.printers import pretty
from kdrag.smt import (
    And,
    BoolSort,
    BoolVal,
    Const,
    Consts,
    DeclareSort,
    Eq,
    Exists,
    ForAll,
    Function,
    If,
    Implies,
    Lambda,
    Not,
    Or,
)
import functools

ZFSet = DeclareSort("ZFSet")
Set = ZFSet
A, B, x, y, z = Consts("A B x y z", ZFSet)
a, b, c, d, p = FreshVars("a b c d p", ZFSet)

Class = ZFSet >> BoolSort()
P, Q = Consts("P Q", Class)

elem = Function("∈", ZFSet, ZFSet, BoolSort())
elts = define("ZF.elts", [A], Lambda([x], elem(x, A)))

zf_db = []

kd.notation.getitem.register(ZFSet, lambda A, x: elem(x, A))

reflects = define("reflects", [P, A], ForAll([x], elem(x, A) == P[x]))
is_set = define("is_set", [P], Exists([A], reflects(P, A)))


# general comprehension is not true. This is Russell's paradox.
@Theorem(Not(ForAll([P], is_set(P))))
def russell(l):
    l.unfold(is_set).unfold(reflects)
    l.assumes(ForAll([P], Exists([A], ForAll([x], elem(x, A) == P[x]))))
    Q = Lambda([x], Not(elem(x, x)))
    l.have(Exists([A], ForAll([x], elem(x, A) == Q[x])))
    l.specialize(0, Q, keep=True)
    l.auto()
    A1 = l.obtain(-1)
    l.have(elem(A1, A1) == Q(A1))
    l.specialize(-1, A1, keep=True)
    l.auto()
    l.show(BoolVal(False), by=[])


def slemma(thm, by=[], **kwargs):
    return prove(thm, by=by + zf_db, **kwargs)


ext_ax = axiom(QForAll([A, B], Eq((A == B), ForAll([x], elem(x, A) == elem(x, B)))))

le = kd.notation.le.define([A, B], QForAll([x], elem(x, A), elem(x, B)))

emp = Const("∅", ZFSet)
elem_emp = axiom(ForAll([x], elem(x, emp) == BoolVal(False)))


# l = kd.Lemma(smt.ForAll([A], (A == emp) == smt.Not(smt.Exists([x], elem(x, A)))))
@kd.tactics.Theorem(ForAll([A], (A == emp) == Not(Exists([x], elem(x, A)))))
def emp_exists_elem(l):
    _A = l.fix()
    l.split()
    with l.sub() as l1:
        l1.intros()
        l1.intros()
        _x = l1.obtain(-1)
        l1.show(BoolVal(False), by=[ext_ax, elem_emp])
    with l.sub() as l2:
        l2.intros()
        l2.rw(ext_ax)
        _x = l2.fix()
        l2.apply(0)
        l2.exists(_x)
        l2.have(elem(_x, emp) == BoolVal(False), by=[elem_emp(_x)])
        l2.have(elem(_x, _A), by=[])

        l2.auto()


# emp_exists_elem = l.qed()


l = Lemma(ForAll([A], Implies((A != emp), Exists([x], elem(x, A)))))
_A = l.fix()
l.auto(by=[emp_exists_elem(_A)])
l.qed()
not_emp_exists_elem = l.qed()

pf1 = prove(Exists([x], Implies(a != emp, elem(x, a))), by=[emp_exists_elem(a)])
(skolem,), elem_pick0 = kd.tactics.skolem(pf1)
# Note that pick(emp) is undefined. You will not be able to prove anything about it.
pick = define("pick", [a], skolem)


elem_pick = prove(
    Implies(a != emp, elem(pick(a), a)), unfold=1, by=[elem_pick0]
).forall([a])


upair = Function("upair", ZFSet, ZFSet, ZFSet)
elem_upair = axiom(QForAll([x, y, z], elem(z, upair(x, y)) == Or(z == x, z == y)))

l = Lemma(ForAll([a, b], Not(upair(a, b) == emp)))
_a, _b = l.fixes()
l.rw(ext_ax)
l.intros()
l.have(elem(_a, upair(_a, _b)), by=[elem_upair(_a, _b, _a)])
l.have(Not(elem(_a, emp)), by=[elem_emp(_a)])
l.auto()
upair_not_emp = l.qed()

l = Lemma(ForAll([a, b], upair(a, b) == upair(b, a)))
l.fixes()
l.rw(ext_ax)
l.fix()
l.rw(elem_upair)
l.rw(elem_upair)
l.auto()
upair_comm = l.qed()

elem_upair_1 = prove(
    ForAll([a, b], elem(a, upair(a, b)) == BoolVal(True)), by=[elem_upair]
)
elem_upair_2 = prove(
    ForAll([a, b], elem(b, upair(a, b)) == BoolVal(True)), by=[elem_upair]
)


@kd.tactics.Theorem(
    ForAll(
        [a, b, c, d],
        (upair(a, b) == upair(c, d)) == Or(And(a == c, b == d), And(a == d, b == c)),
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


pick_upair = prove(
    ForAll([a, b], Or(pick(upair(a, b)) == a, pick(upair(a, b)) == b)),
    by=[elem_pick, elem_upair, elem_emp],
)


sing = define("ZF.sing", [x], upair(x, x))


def FinSet(*xs):
    """
    A helper for sets of the form {x1, x2, ..., xn}
    """
    return functools.reduce(lambda a, b: sing(b) | a, xs, emp)


@kd.tactics.Theorem(ForAll([a, b], elem(a, sing(b)) == (a == b)))
def elem_sing(l):
    a, b = l.fixes()
    l.unfold(sing)
    l.auto(by=[elem_upair])


sing_not_emp = prove(Not(sing(a) == emp), unfold=1, by=[upair_not_emp]).forall([a])


@kd.tactics.Theorem(ForAll([a], pick(sing(a)) == a))
def pick_sing(l):
    _a = l.fix()
    l.unfold(sing)
    l.auto(by=[pick_upair])
    # l.rw(ext_ax)
    # _x = l.fix()
    # l.auto(by=[elem_sing, elem_pick, elem_emp])


# Separation

sep = Function("sep", ZFSet, Class, ZFSet)
elem_sep = axiom(QForAll([P, A, x], elem(x, sep(A, P)) == And(P[x], elem(x, A))))


@Theorem(
    QForAll(
        [a, b, P],
        sep(upair(a, b), P)
        == If(P(a), If(P(b), upair(a, b), sing(a)), If(P(b), sing(b), emp)),
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

bigunion = Function("bigunion", ZFSet, ZFSet)  # ⋃
bigunion_ax = axiom(
    QForAll([A, x], Eq(elem(x, bigunion(A)), QExists([B], elem(B, A), elem(x, B))))
)


# Binary Union

union = define("union", [A, B], bigunion(upair(A, B)))
kd.notation.or_.register(Set, union)

l = Lemma(a | b == b | a)
l.unfold(union)
l.rw(ext_ax)
_x = l.fix()
l.auto(by=[elem_upair, bigunion_ax])
union_comm = l.qed().forall([a, b])

l = Lemma(
    ForAll([x, A, B], elem(x, bigunion(upair(A, B))) == (elem(x, A) | elem(x, B)))
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


l = Lemma(ForAll([x, A, B], elem(x, A | B) == (elem(x, A) | elem(x, B))))
_x, _A, _B = l.fixes()
l.unfold(union)
l.rw(elem_bigunion_upair)
l.auto()
elem_union = l.qed()


l = Lemma(ForAll([a, b, c], (a | b) | c == a | (b | c)))
_a, _b, _c = l.fixes()
l.rw(ext_ax)
_x = l.fix()
l.rw(elem_union)
l.rw(elem_union)
l.rw(elem_union)
l.rw(elem_union)
l.auto()
union_assoc = l.qed()

l = Lemma(ForAll([a], a | a == a))
l.fixes()
l.rw(ext_ax)
l.fix()
l.rw(elem_union)
l.auto()
union_idem = l.qed()

l = Lemma(ForAll([a, b, c], a <= a | b))
l.fixes()
l.unfold(le)
l.fix()
l.rw(elem_union)
l.auto()
le_union = l.qed()


@kd.tactics.Theorem(ForAll([a, b], sing(a) | upair(a, b) == upair(a, b)))
def sing_union_upair(l):
    a, b = l.fixes()
    l.rw(ext_ax)
    l.fix()
    l.rw(elem_union)
    l.rw(elem_upair)
    l.rw(elem_sing)
    l.auto()


@kd.tactics.Theorem(ForAll([a, b], bigunion(upair(a, b)) == a | b))
def bigunion_upair(l):
    a, b = l.fixes()
    l.rw(ext_ax)
    _ = l.fix()
    l.rw(elem_bigunion_upair)
    l.rw(elem_union)
    l.auto()


# Biginter
biginter = define(
    "biginter",
    [a],
    sep(pick(a), Lambda([x], QForAll([b], elem(b, a), elem(x, b)))),
)
# huh. biginter(emp) is undefined since we can't pick from it.
l = Lemma(
    ForAll(
        [A, x],
        Implies(A != emp, elem(x, biginter(A)) == QForAll([b], elem(b, A), elem(x, b))),
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

inter = define("inter", [A, B], sep(A, Lambda([x], elem(x, B))))
kd.notation.and_.register(Set, inter)

l = Lemma(ForAll([x, A, B], elem(x, A & B) == (elem(x, A) & elem(x, B))))
l.fixes()
l.unfold(inter)
l.rw(elem_sep)
l.auto()
elem_inter = l.qed()

l = Lemma(ForAll([A, B], biginter(upair(A, B)) == inter(A, B)))
_A, _B = l.fixes()
l.rw(ext_ax)
l.have(upair(_A, _B) != emp, by=[upair_not_emp(_A, _B)])
_x = l.fix()
l.rw(elem_inter)
l.auto(by=[elem_biginter, elem_upair])
biginter_upair_inter = l.qed()

l = Lemma(ForAll([A, B], A & B == B & A))
l.fixes()
l.rw(ext_ax)
l.fix()
l.rw(elem_inter)
l.rw(elem_inter)
l.auto()
inter_comm = l.qed()

l = Lemma(ForAll([a, b, c], (a & b) & c == a & (b & c)))
l.fixes()
l.rw(ext_ax)
l.fix()
l.rw(elem_inter)
l.rw(elem_inter)
l.rw(elem_inter)
l.rw(elem_inter)
l.auto()
inter_assoc = l.qed()


l = Lemma(ForAll([a], a & a == a))
l.fixes()
l.rw(ext_ax)
l.fix()
l.rw(elem_inter)
l.auto()
inter_idem = l.qed()


l = Lemma(ForAll([a, b, c], a & (b | c) == (a & b) | (a & c)))
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

l = Lemma(ForAll([a, b], a & b <= a))
l.fixes()
l.unfold(le)
l.fix()
l.rw(elem_inter)
l.auto()
inter_le = l.qed()


@Theorem(ForAll([a, b, x], (x <= (a & b)) == ((x <= a) & (x <= b))))
def le_inter_2(l):
    a, b, x = l.fixes()
    l.unfold(le)
    l.split()
    l.auto(by=[elem_inter])
    l.auto(by=[elem_inter])


l = Lemma(ForAll([x], x & emp == emp))
l.fixes()
l.rw(ext_ax)
l.fix()
l.rw(elem_inter)
l.rw(elem_emp)
l.auto()
inter_emp = l.qed()


l = Lemma(ForAll([a, b, c], (a | b) & c == (a & c) | (b & c)))
l.fixes()
l.auto(by=[inter_comm, inter_union_distr])
union_inter_distr = l.qed()


@kd.tactics.Theorem(
    ForAll(
        [a, b, c],
        inter(a, upair(b, c))
        == If(
            elem(b, a),
            If(elem(c, a), upair(b, c), sing(b)),
            If(elem(c, a), sing(c), emp),
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


inter_upair_1 = prove(
    ForAll(
        [a, b, c],
        inter(upair(b, c), a)
        == If(
            elem(b, a),
            If(elem(c, a), upair(b, c), sing(b)),
            If(elem(c, a), sing(c), emp),
        ),
    ),
    by=[inter_upair_2, inter_comm],
)

# Difference

sub = kd.notation.sub.define([A, B], sep(A, Lambda([x], Not(elem(x, B)))))


@Theorem(QForAll([a, b], upair(a, b) - sing(a) == If(a == b, emp, sing(b))))
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

pow = Function("pow", ZFSet, ZFSet)
elem_pow = axiom(ForAll([A, x], elem(x, pow(A)) == (x <= A)))


@Theorem(ForAll([a, b], pow(a & b) == pow(a) & pow(b)))
def pow_inter(l):
    a, b = l.fixes()
    l.rw(ext_ax).fix()
    l.rw(elem_inter).rw(elem_pow).rw(elem_pow).rw(elem_pow).rw(le_inter_2)
    l.auto()


# Ordered Pair


pair = define("pair", [a, b], upair(sing(a), upair(a, b)))
is_pair = define("is_pair", [c], Exists([a, b], pair(a, b) == c))
fst = define("fst", [p], pick(biginter(p)))
snd = define(
    "snd",
    [p],
    If(sing(sing(fst(p))) == p, fst(p), pick(bigunion(p) - sing(fst(p)))),
)


@Theorem(ForAll([a, b], is_pair(pair(a, b)) == BoolVal(True)))
def is_pair_pair(l):
    a, b = l.fixes()
    l.unfold(is_pair)
    l.auto()


@kd.tactics.Theorem(
    ForAll([a, b, c, d], (pair(a, b) == pair(c, d)) == And(a == c, b == d))
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


@kd.tactics.Theorem(ForAll([a, b], fst(pair(a, b)) == a))
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


@kd.tactics.Theorem(ForAll([a, b], snd(pair(a, b)) == b))
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
    l.have((a == b) == BoolVal(False))
    l.unfold(pair, at=0)
    l.unfold(sing, at=0)
    l.auto(by=[upair_inj])
    l.rw(-1)
    l.simp()
    l.rw(pick_sing)
    l.auto()


@kd.tactics.Theorem(
    ForAll([a, b, x], elem(x, pair(a, b)) == Or(x == sing(a), x == upair(a, b)))
)
def elem_pair(l):
    a, b, c = l.fixes()
    l.unfold(pair)
    l.rw(elem_upair)
    l.auto()


# Cartesian product
prod = define(
    "prod",
    [A, B],
    sep(
        pow(pow(A | B)),
        Lambda(
            [p],
            QExists([x, y], And(elem(x, A), elem(y, B)), p == pair(x, y)),
        ),
    ),
)

kd.notation.mul.register(Set, prod)


@Theorem(
    ForAll(
        [A, B, p],
        elem(p, prod(A, B))
        == And(
            QExists([x, y], And(elem(x, A), elem(y, B)), p == pair(x, y)),
            elem(p, pow(pow(A | B))),
        ),
    )
)
def elem_prod_def(l):
    _A, _B, _p = l.fixes()
    l.unfold(prod)
    l.rw(elem_sep)
    l.auto()


@Theorem(
    ForAll(
        [A, B, p],
        elem(p, prod(A, B))
        == And(
            elem(fst(p), A),
            elem(snd(p), B),
            p == pair(fst(p), snd(p)),
        ),
    )
)
def elem_prod(l):
    A, B, p = l.fixes()
    l.split()

    # -> direction: extract witnesses from the product definition.
    l.intros()
    l.rw(elem_prod_def, at=0)
    l.split(at=0)
    x1, y1 = l.obtain(0)
    l.split(at=0)
    l.split()
    l.rw(1)
    l.rw(fst_pair)
    l.auto()
    l.rw(1)
    l.rw(snd_pair)
    l.auto()
    l.rw(1)
    l.rw(fst_pair)
    l.rw(snd_pair)
    l.auto()

    # <- direction: use fst/snd as witnesses and show the pair lives in pow(pow(A | B)).
    l.intros()
    l.split(at=0)
    l.rw(elem_prod_def)
    l.split()
    l.exists(fst(p), snd(p))
    l.auto()
    l.rw(elem_pow)
    l.rw(-1)
    l.unfold(le)
    _z = l.fix()
    l.intros()
    l.rw(elem_pair, at=-1)
    l.split(at=-1)

    # z = {fst(p), snd(p)} -> {fst(p), snd(p)} ⊆ A | B.
    l.rw(-1)
    l.rw(elem_pow)
    l.unfold(le)
    _w = l.fix()
    l.intros()
    l.rw(elem_upair, at=-1)
    l.split(at=-1)
    l.rw(-1)
    l.rw(elem_union)
    l.auto()
    l.rw(-1)
    l.rw(elem_union)
    l.auto()

    # z = {fst(p)} -> {fst(p)} ⊆ A | B.
    l.rw(-1)
    l.rw(elem_pow)
    l.unfold(le)
    _w = l.fix()
    l.intros()
    l.rw(elem_sing, at=-1)
    l.rw(elem_union)
    l.rw(-1)
    l.auto()


R = Const("R", ZFSet)
# Relations
is_rel = define("is_rel", [R], ForAll([p], Implies(elem(p, R), is_pair(p))))

dom = define(
    "dom",
    [R],
    sep(
        bigunion(bigunion(R)),
        Lambda([x], QExists([y], elem(pair(x, y), R))),
    ),
)

ran = define(
    "ran",
    [R],
    sep(
        bigunion(bigunion(R)),
        Lambda([y], QExists([x], elem(pair(x, y), R))),
    ),
)


false = define("zf.false", [], emp)
true = define("zf.true", [], sing(emp))
Bool = upair(true, false)

zero = define("zf.zero", [], emp)
succ = define("zf.succ", [x], x | sing(x))


pretty.register_infix(elem, "∈", 4)
pretty.register_infix(le, "⊆", 4)
pretty.register_infix(union, "∪", 5, association="right", breaks=True)
pretty.register_infix(inter, "∩", 6, association="right", breaks=True)
pretty.register_infix(sub, "∖", 5)
pretty.register_infix(prod, "×", 7, association="left")


def test():
    """
    >>> True
    True
    """
