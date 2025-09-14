import kdrag as kd
import kdrag.smt as smt
import kdrag.theories.set as set_

IntSet = set_.Set(smt.IntSort())
computable = smt.Function("computable", IntSet, smt.BoolSort())


# bounded quantifiers
# Can define them actually
n, m = smt.Ints("n m")
A, B = smt.Consts("A B", IntSet)
bexists = smt.Function("bexists", IntSet, smt.IntSort(), smt.BoolSort())
bexists = kd.define(
    "bexist", [A, n], smt.If(n < 0, False, smt.Or(A[n], bexists(A, n - 1)))
)

bforall = smt.Function("bforall", IntSet, smt.IntSort(), smt.BoolSort())
bforall = kd.define(
    "bforall", [A, n], smt.If(n < 0, True, smt.And(A[n], bforall(A, n - 1)))
)

# Kleene mu operator
# https://en.wikipedia.org/wiki/%CE%9C_operator
mu_iter = smt.Function("mu_iter", IntSet, smt.IntSort(), smt.IntSort())
mu_iter = kd.define("mu_iter", [A, n], smt.If(A[n], n, mu_iter(A, n + 1)))
mu = kd.define("mu", [A], mu_iter(A, 0))

"""
# https://isabelle.in.tum.de/library/HOL/HOL-Library/Countable_Set.html
f = smt.Function("f", smt.IntSort(), A)
countable = kd.define(
    "countable", [A], smt.Exists([f], smt.ForAll([x], smt.Exists[m])
)"


SKI combinators

Krivine Machine


"""


# https://en.wikipedia.org/wiki/Computably_enumerable_set
