import kdrag as kd
from kdrag import QForAll, prove
import kdrag.smt as smt
from kdrag.smt import And, Consts, ForAll, IntSort, Ints, Not

import kdrag.contrib.junk_drawer.generic as generic


class PreOrder(generic.TypeClass):
    key: smt.SortRef
    refl: kd.Proof
    trans: kd.Proof
    less_le_not_le = kd.Proof

    def check(self, T):
        x, y, z = Consts("x y z", T)
        assert kd.utils.alpha_eq(self.refl.thm, ForAll([x], x <= x))
        assert kd.utils.alpha_eq(
            self.trans.thm, QForAll([x, y, z], x <= y, y <= z, x <= z)
        )
        assert kd.utils.alpha_eq(
            self.less_le_not_le.thm,
            QForAll([x, y], (x < y) == And(x <= y, Not(y <= x))),
        )


n, m, k = Ints("n m k")
PreOrder.register(
    IntSort(),
    refl=prove(ForAll([n], n <= n)),
    trans=prove(QForAll([n, m, k], n <= m, m <= k, n <= k)),
    less_le_not_le=prove(QForAll([n, m], (n < m) == And(n <= m, Not(m <= n)))),
)
