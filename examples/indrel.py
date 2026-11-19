"""Integer less-than as a least inductive relation.

Run: PYTHONPATH=src python examples/indrel.py
"""

from kdrag import Lemma, indrel, prove
from kdrag.smt import And, BoolSort, ForAll, Function, Ints, IntSort, Lambda

x, y = Ints("indrel_x indrel_y")
lt = Function("indrel_lt", IntSort(), IntSort(), BoolSort())
lt = indrel(
    "indrel_lt", [x, y], And(x >= 0, x == 0, y > 0), And(x >= 0, lt(x - 1, y - 1))
)
prove(lt(0, 1), by=[lt.case0])
prove(lt(1, 2), by=[lt.case0, lt.case1])
invariant = Lambda([x, y], And(x >= 0, x < y))
prove(ForAll([x, y], lt(x, y), And(x >= 0, x < y)), by=[lt.induct(invariant)])
# Keep y general while inducting on x so it can decrease in the IH.
pf = Lemma(ForAll(x, ForAll(y, And(x >= 0, x < y), lt(x, y))))
a = pf.fix()
pf.induct(a)
a = pf.fix()
pf.intros()
_b = pf.fix()
pf.intro()
pf.auto()
_b = pf.fix()
pf.intro()
pf.auto(by=[lt.case0])
a = pf.fix()
pf.intros()
_b = pf.fix()
pf.intro()
pf.auto(by=[lt.case1])
complete = pf.qed()
prove(
    ForAll([x, y], lt(x, y) == And(x >= 0, x < y)),
    by=[complete, lt.induct(invariant)],
)
pf = Lemma(lt(0, 1))
pf.unfold(lt)
pf.auto()
pf.qed()

print(lt.defn)
