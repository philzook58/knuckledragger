from kdrag import define
from kdrag.smt import And, BoolSort, Consts, Function, If, IntSort, Ints, Or
import kdrag.theories.set as set_

IntSet = set_.Set(IntSort())
computable = Function("computable", IntSet, BoolSort())


# bounded quantifiers
# Can define them actually
n, m = Ints("n m")
A, B = Consts("A B", IntSet)
bexists = Function("bexists", IntSet, IntSort(), BoolSort())
bexists = define("bexist", [A, n], If(n < 0, False, Or(A[n], bexists(A, n - 1))))

bforall = Function("bforall", IntSet, IntSort(), BoolSort())
bforall = define("bforall", [A, n], If(n < 0, True, And(A[n], bforall(A, n - 1))))

# Kleene mu operator
# https://en.wikipedia.org/wiki/%CE%9C_operator
mu_iter = Function("mu_iter", IntSet, IntSort(), IntSort())
mu_iter = define("mu_iter", [A, n], If(A[n], n, mu_iter(A, n + 1)))
mu = define("mu", [A], mu_iter(A, 0))

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
