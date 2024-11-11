import kdrag as kd
import kdrag.smt as smt

ZFSet = smt.DeclareSort("ZFSet")
A, B, x, y, z = smt.Consts("A B x y z", ZFSet)
elem = smt.Function("elem", ZFSet, ZFSet, smt.BoolSort())
Class = ZFSet >> smt.BoolSort()
P, Q = smt.Consts("P Q", Class)
klass = kd.define("klass", [A], smt.Lambda([x], elem(x, A)))

zf_db = []


def slemma(thm, by=[], **kwargs):
    return kd.lemma(thm, by=by + zf_db, **kwargs)


emp = smt.Const("emp", ZFSet)
emp_ax = kd.axiom(smt.ForAll([x], smt.Not(elem(x, emp))))

upair = smt.Function("upair", ZFSet, ZFSet, ZFSet)
upair_ax = kd.axiom(
    kd.QForAll([x, y, z], elem(z, upair(x, y)) == smt.Or(z == x, z == y))
)

ext_ax = kd.axiom(
    kd.QForAll([A, B], smt.ForAll([x], elem(x, A) == elem(x, B)) == (A == B))
)

sep = smt.Function("sep", ZFSet, Class, ZFSet)
sep_ax = kd.axiom(
    kd.QForAll([P, A, x], elem(x, sep(A, P)) == smt.And(P[x], elem(x, A)))
)

zf_db.extend([emp_ax, upair_ax, ext_ax, sep_ax])
le = kd.notation.le.define([A, B], kd.QForAll([x], elem(x, A), elem(x, B)))
