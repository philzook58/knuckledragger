import kdrag as kd
import kdrag.smt as smt

import kdrag.contrib.junk_drawer.generic as generic


class PreOrder(generic.TypeClass):
    key: smt.SortRef
    refl: kd.Proof
    trans: kd.Proof
    less_le_not_le = kd.Proof

    def check(self, T):
        x, y, z = smt.Consts("x y z", T)
        assert kd.utils.alpha_eq(self.refl.thm, smt.ForAll([x], x <= x))
        assert kd.utils.alpha_eq(
            self.trans.thm, kd.QForAll([x, y, z], x <= y, y <= z, x <= z)
        )
        assert kd.utils.alpha_eq(
            self.less_le_not_le.thm,
            kd.QForAll([x, y], (x < y) == smt.And(x <= y, smt.Not(y <= x))),
        )


n, m, k = smt.Ints("n m k")
PreOrder.register(
    smt.IntSort(),
    refl=kd.prove(smt.ForAll([n], n <= n)),
    trans=kd.prove(kd.QForAll([n, m, k], n <= m, m <= k, n <= k)),
    less_le_not_le=kd.prove(
        kd.QForAll([n, m], (n < m) == smt.And(n <= m, smt.Not(m <= n)))
    ),
)
