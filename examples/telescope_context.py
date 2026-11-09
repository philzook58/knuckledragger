"""Compare explicit telescopes with the existing global schematic variables.

The wrapper keeps a kernel proof of the internalized judgment. Opening and
closing reuse it; weakening and substitution currently ask Z3 for a new proof.
"""

from kdrag import define, prove as prove_closed
from kdrag.contrib.telescope import Hyp, ScopedProof, Vars, prove
from kdrag.smt import ForAll, RealVal, Reals

# Ordinary named constants become local through their explicit context.
x, y = Reals("x y")
ctx = (Vars((x,)), Hyp(x > 0))
inc = define("telescope_inc", [x], x + 1)
positive = prove(x > 0, ctx=ctx)
result = prove(inc(x) > 0, ctx=ctx, by=[positive, inc.defn])
print("Local judgment:", result)
print("Closed theorem:", result.close().close().closed)

# Move one simultaneous binder block and one implication onto the left.
source = ScopedProof.from_proof(prove_closed(ForAll([x, y], x > y, x + 1 > y)))
a, b = Reals("a b")
opened = source.fix((a, b)).intro()
print("Named binders:", opened)
assert opened.close().close().closed is source.closed

# Instantiate a block, including occurrences in the later assumptions.
instantiated = opened.subst(0, (RealVal(3), RealVal(2)))
print("Substituted judgment:", instantiated)
print("Internalized:", instantiated.to_expr())
