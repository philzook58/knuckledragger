"""Integer less-than as an intersection of closed relations.

Run: PYTHONPATH=src python examples/indrel.py
"""

from kdrag import Lemma, define_least, prove, relation_operator
from kdrag.smt import (
    And,
    ArraySort,
    BoolSort,
    Consts,
    ForAll,
    Function,
    Ints,
    IntSort,
    Lambda,
)

x, y = Ints("x y")
lt = Function("example_lt", IntSort(), IntSort(), BoolSort())
clauses = (And(x >= 0, x == 0, y > 0), And(x >= 0, lt(x - 1, y - 1)))
F = relation_operator(lt, [x, y], *clauses)
lt = define_least(lt, [x, y], *clauses)
R, S = Consts("R S", ArraySort(IntSort(), IntSort(), BoolSort()))

# Optional monotonicity proof, independent of constructing the intersection.
monotone = prove(
    ForAll(
        [R, S], ForAll([x, y], R(x, y), S(x, y)), ForAll([x, y], F(R)(x, y), F(S)(x, y))
    )
)

# Any closed relation contains the intersection: choose it in the definition.
pf = Lemma(
    ForAll(R, ForAll([x, y], F(R)(x, y), R(x, y)), ForAll([x, y], lt(x, y), R(x, y)))
)
R = pf.fix()
pf.intro()
pf.fixes()
h = pf.intro()
pf.unfold(lt, at=h)
h = pf.top_goal().ctx[-1]
pf.specialize(h, R)
pf.auto()
least = pf.qed()

# The arithmetic relation is closed, so lt is contained in it.
nonnegative_lt = Lambda([x, y], And(x >= 0, x < y))
sound = prove(ForAll([x, y], lt(x, y), And(x >= 0, x < y)), by=[least(nonnegative_lt)])
print(sound)
