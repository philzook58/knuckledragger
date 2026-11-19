"""Integer less-than as a least inductive relation.

Run: PYTHONPATH=src python examples/indrel.py
"""

from kdrag import Lemma, define_least, prove, prove_monotone, prove_unfolding
from kdrag.kernel import make_unfolding, register_definition
from kdrag.smt import And, BoolSort, ForAll, Function, Ints, IntSort, Lambda

x, y = Ints("indrel_x indrel_y")
lt = Function("indrel_lt", IntSort(), IntSort(), BoolSort())
lt = define_least(
    "indrel_lt", [x, y], And(x >= 0, x == 0, y > 0), And(x >= 0, lt(x - 1, y - 1))
)
# The intersection and induction theorem exist before proving monotonicity.
mono = prove_monotone(lt)
unfolding = prove_unfolding(lt, mono)
register_definition(make_unfolding(unfolding))

prove(lt(0, 1), by=[lt.defn])
prove(lt(1, 2), by=[lt.defn])
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
pf.auto(by=[lt.defn])
a = pf.fix()
pf.intros()
_b = pf.fix()
pf.intro()
pf.auto(by=[lt.defn])
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
