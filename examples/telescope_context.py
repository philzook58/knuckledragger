"""Compare explicit telescopes with the existing global schematic variables.

The wrapper keeps a kernel proof of the internalized judgment. Opening and
closing reuse it. All-variable weakening uses existing kernel rules; mixed
contexts and substitution currently ask Z3 for a new proof.
"""

from kdrag import define, prove as prove_closed
from kdrag.contrib.telescope import (
    Context,
    Hyp,
    ScopedProof,
    Subst,
    Vars,
    lift,
    prove,
    variables,
)
from kdrag.smt import ForAll, RealSort, RealVal, Reals

# Local terms carry their context through arithmetic and function calls.
(x,) = variables("x", RealSort())
x = x.weaken((x > 0).assume())
inc = define("telescope_inc", [x.raw], x.raw + 1)
positive = prove(x > 0)
result = prove(lift(inc, x) > 0, by=[positive, inc.defn])
print("Local judgment:", result)
print("Scoped proposition:", result.expr)
print("Closed theorem:", result.close().close().closed)

# Move one simultaneous binder block and one implication onto the left.
x, y = Reals("x y")
source = ScopedProof.from_proof(prove_closed(ForAll([x, y], x > y, x + 1 > y)))
a, b = Reals("a b")
opened = source.fix((a, b)).intro()
print("Named binders:", opened)
assert opened.close().close().closed is source.closed

# Instantiate a block, including occurrences in the later assumptions.
instantiated = opened.subst(0, (RealVal(3), RealVal(2)))
print("Substituted judgment:", instantiated)
print("Internalized:", instantiated.to_expr())

# A mixed forest supplies both a term and evidence for its instantiated premise.
(a,) = variables("forest_a", RealSort())
a = a.weaken((a > 1).assume())
(x,) = Reals("forest_x")
destination = Context.of(Vars((x,)), Hyp(x > 0))
sigma = Subst(a.ctx, destination, ((a - 1,), prove(a - 1 > 0)))
print("Term/proof forest:", sigma.values)
print("Transported proof:", sigma.apply(prove(x + 1 > 0, ctx=destination)))
