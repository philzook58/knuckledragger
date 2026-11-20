"""Integer less-than as an intersection of closed relations.

Run: PYTHONPATH=src python examples/indrel.py
"""

from kdrag import (
    Theorem,
    define_least,
    prove,
    relation_operator,
    least_induct,
    least_unfold,
)
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
@Theorem(
    ForAll(R, ForAll([x, y], F(R)(x, y), R(x, y)), ForAll([x, y], lt(x, y), R(x, y)))
)
def least(pf):
    R = pf.fix()
    pf.intro()
    pf.fixes()
    h = pf.intro()
    pf.unfold(lt, at=h)
    h = pf.top_goal().ctx[-1]
    pf.specialize(h, R)
    pf.auto()


# The arithmetic relation is closed, so lt is contained in it.
nonnegative_lt = Lambda([x, y], And(x >= 0, x < y))


@Theorem(ForAll([x, y], lt(x, y), And(x >= 0, x < y)))
def sound(pf):
    pf.specialize(least, nonnegative_lt)
    pf.beta(at=-1)
    pf.apply(-1)
    pf.fixes()
    pf.intro()
    pf.auto()


print(sound)

# Optional generators consume F, with no changes to the named definition.
induction = least_induct(F)
unfolding_if_monotone = least_unfold(F)
unfolding = unfolding_if_monotone(prove(unfolding_if_monotone.thm.arg(0)))
