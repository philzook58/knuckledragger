import kdrag as kd
import kdrag.smt as smt

from kdrag.contrib.junk_drawer.generic import TypeClass


# https://isabelle.in.tum.de/library/HOL/HOL/Groups.html
class Semigroup(TypeClass):
    key: smt.SortRef
    assoc: kd.Proof

    def check(self, T):
        # All of these are kind of redundant
        # assert isinstance(T, smt.SortRef)
        # assert T in kd.notation.mul or hasattr(smt.FreshConst(T), "__mul__")
        # assert self.key in property.assoc
        x, y, z = smt.Consts("x y z", T)
        assert kd.utils.alpha_eq(
            self.assoc.thm, smt.ForAll([x, y, z], x * (y * z) == (x * y) * z)
        )


n, m, k = smt.Ints("n m k")
Semigroup.register(
    smt.IntSort(), assoc=kd.prove(smt.ForAll([n, m, k], n * (m * k) == (n * m) * k))
)


class AbelSemiGroup(TypeClass):
    key: smt.SortRef
    comm: kd.Proof

    def check(self, T):
        self.Semigroup = Semigroup(T)
        x, y, z = smt.Consts("x y z", T)
        assert kd.utils.alpha_eq(self.comm.thm, smt.ForAll([x, y], x * y == y * x))
        self.assoc = self.Semigroup.assoc
        self.left_commute = kd.prove(
            smt.ForAll([x, y, z], x * (y * z) == y * (x * z)),
            by=[self.comm, self.assoc],
        )


AbelSemiGroup.register(smt.IntSort(), comm=kd.prove(smt.ForAll([n, m], n * m == m * n)))


class Monoid(TypeClass):
    e: smt.ExprRef
    id_left: kd.Proof
    id_right: kd.Proof

    def check(self, T):
        self.Semigroup = Semigroup(T)
        self.assoc = self.Semigroup.assoc
        x = smt.Const("x", T)
        assert kd.utils.alpha_eq(self.id_left.thm, smt.ForAll([x], self.e * x == x))
        assert kd.utils.alpha_eq(self.id_right.thm, smt.ForAll([x], x * self.e == x))


Monoid.register(
    smt.IntSort(),
    e=smt.IntVal(1),
    id_left=kd.prove(smt.ForAll([n], 1 * n == n)),
    id_right=kd.prove(smt.ForAll([n], n * 1 == n)),
)


class Group(TypeClass):
    inv: smt.FuncDeclRef
    inv_left: kd.Proof
    inv_right: kd.Proof

    def check(self, T):
        self.Monoid = Monoid(T)
        self.e = self.Monoid.e
        self.assoc = self.Monoid.assoc
        x = smt.Const("x", T)
        assert kd.utils.alpha_eq(
            self.inv_left.thm, smt.ForAll([x], self.inv(x) * x == self.e)
        )
        assert kd.utils.alpha_eq(
            self.inv_right.thm, smt.ForAll([x], x * self.inv(x) == self.e)
        )


# https://en.wikipedia.org/wiki/Group_(mathematics)

G = smt.DeclareSort("G")
mul = smt.Function("mul", G, G, G)
kd.notation.mul.register(G, mul)
e = smt.Const("e", G)
inv = smt.Function("inv", G, G)
x, y, z = smt.Consts("x y z", G)

mul_assoc = kd.axiom(smt.ForAll([x, y, z], x * (y * z) == (x * y) * z))
id_left = kd.axiom(smt.ForAll([x], e * x == x))
inv_left = kd.axiom(smt.ForAll([x], inv(x) * x == e))

Semigroup.register(G, assoc=mul_assoc)

x, y, z = kd.tactics.FreshVars("x y z", G)

c = kd.Calc([], e, assume=[smt.ForAll([y], y * x == y)])
c.eq(e * x)
c.eq(x, by=[id_left(x)], timeout=2000)
id_unique1 = c.qed().forall([x])

c = kd.Calc([x], x * inv(x))
c.eq(e * (x * inv(x)), by=[id_left])
c.eq((inv(inv(x)) * inv(x)) * (x * inv(x)), by=[inv_left])
c.eq(inv(inv(x)) * ((inv(x) * x) * inv(x)), by=[mul_assoc])
c.eq(inv(inv(x)) * (e * inv(x)), by=[inv_left])
c.eq(inv(inv(x)) * inv(x), by=[id_left])
c.eq(e, by=[inv_left])
inv_right = c.qed()

c = kd.Calc([x], x * e)
c.eq(x * (inv(x) * x), by=[inv_left])
c.eq((x * inv(x)) * x, by=[mul_assoc])
c.eq(e * x, by=[inv_right])
c.eq(x, by=[id_left])
id_right = c.qed()

Monoid.register(
    G,
    e=e,
    id_left=id_left,
    id_right=id_right,
)

Group.register(
    G,
    inv=inv,
    inv_left=inv_left,
    inv_right=inv_right,
)
# c = kd.Calc([x], e, assume=[smt.ForAll([y], x * y == y)])
# c.eq(x * e)
# c.eq(x, by=[id_right])
# id_unique2 = c.qed()
l = kd.Lemma(kd.QForAll([x], kd.QForAll([y], x * y == y), x == e))
_x = l.fix()
l.intros()
l.eq(_x * e)
l.eq(_x, by=[id_right(_x)])
id_unique2 = l.qed()

c = kd.Calc([x, y], y, assume=[y * x == e])
c.eq(y * e, by=[id_right])
c.eq(y * (x * inv(x)), by=[inv_right])
c.eq((y * x) * inv(x), by=[mul_assoc])
c.eq(e * inv(x), by=[inv_right])
c.eq(inv(x), by=[id_left])
inv_unique1 = c.qed()


abelian = kd.define("abelian", [], smt.ForAll([x, y], x * y == y * x))
