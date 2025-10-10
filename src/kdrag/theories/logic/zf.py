import kdrag as kd
import kdrag.smt as smt

ZFSet = smt.DeclareSort("ZFSet")
Set = ZFSet
A, B, x, y, z = smt.Consts("A B x y z", ZFSet)

a, b, c = kd.FreshVars("a b c", ZFSet)
elem = smt.Function("elem", ZFSet, ZFSet, smt.BoolSort())
Class = ZFSet >> smt.BoolSort()
P, Q = smt.Consts("P Q", Class)
klass = kd.define("klass", [A], smt.Lambda([x], elem(x, A)))

zf_db = []

kd.notation.getitem.register(ZFSet, lambda A, x: elem(x, A))


def slemma(thm, by=[], **kwargs):
    return kd.prove(thm, by=by + zf_db, **kwargs)


ext_ax = kd.axiom(
    kd.QForAll([A, B], smt.Eq((A == B), smt.ForAll([x], elem(x, A) == elem(x, B))))
)

emp = smt.Const("emp", ZFSet)
elem_emp = kd.axiom(smt.ForAll([x], elem(x, emp) == smt.BoolVal(False)))

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

sing = kd.define("sing", [x], upair(x, x))


sep = smt.Function("sep", ZFSet, Class, ZFSet)
sep_ax = kd.axiom(
    kd.QForAll([P, A, x], elem(x, sep(A, P)) == smt.And(P[x], elem(x, A)))
)

zf_db.extend([elem_emp, elem_upair, ext_ax, sep_ax])
le = kd.notation.le.define([A, B], kd.QForAll([x], elem(x, A), elem(x, B)))

bigunion = smt.Function("bigunion", ZFSet, ZFSet)
bigunion_ax = kd.axiom(
    kd.QForAll(
        [A, x], smt.Eq(elem(x, bigunion(A)), kd.QExists([B], elem(B, A), elem(x, B)))
    )
)


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
l.rewrite(bigunion_ax)
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
l.rw(sep_ax)
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
l.rw(sep_ax)
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

# Difference

sub = kd.notation.sub.define([A, B], sep(A, smt.Lambda([x], smt.Not(elem(x, B)))))


# Power

pow = smt.Function("pow", ZFSet, ZFSet)
elem_pow = kd.axiom(smt.ForAll([A, x], elem(x, pow(A)) == (x <= A)))


def test():
    """
    >>> True
    True
    """
