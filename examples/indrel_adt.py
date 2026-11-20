"""Least relations on ADTs: even Peano naturals and list membership.

Run: PYTHONPATH=src python examples/indrel_adt.py
"""

from kdrag import (
    Nat,
    ListSort,
    Lemma,
    define_least,
    relation_operator,
    least_induct,
    least_unfold,
    prove,
)
from kdrag.smt import (
    And,
    BoolSort,
    Const,
    Consts,
    DeclareSort,
    Exists,
    Function,
    Lambda,
    Not,
)

# Even(0); Even(n) -> Even(S(S(n))).
n, m = Consts("n m", Nat)
even = Function("ADT.Even", Nat, BoolSort())
even_clauses = (n == Nat.Z, Exists(m, And(n == Nat.S(Nat.S(m)), even(m))))
even_operator = relation_operator(even, n, *even_clauses)
even = define_least(even, n, *even_clauses)
even_induct = least_induct(even_operator)
even_conditional = least_unfold(even_operator)
even_unfold = even_conditional(prove(even_conditional.thm.arg(0)))
even_invariant = even_induct(Lambda(n, n != Nat.S(Nat.Z)))
even_excludes_one = even_invariant(prove(even_invariant.thm.arg(0)))

# Construct a positive instance by choosing arbitrary closed candidate R.
pf = Lemma(even(Nat.S(Nat.S(Nat.Z))))
pf.unfold(even)
pf.fix()
closed = pf.intro()
pf.specialize(closed, Nat.Z, keep=True)
pf.specialize(closed, Nat.S(Nat.S(Nat.Z)), keep=True)
pf.auto()
even_two = pf.qed()

# n != S(0) is closed under both rules; thus the intersection excludes S(0).
pf = Lemma(Not(even(Nat.S(Nat.Z))))
member = pf.intro()
pf.unfold(even, at=member)
pf.specialize(pf.top_goal().ctx[-1], Lambda(n, n != Nat.S(Nat.Z)))
pf.auto()
not_even_one = pf.qed()

# Member(x, Cons(x, xs)); Member(x, xs) -> Member(x, Cons(y, xs)).
Element = DeclareSort("ADT.Member.Element")
List = ListSort(Element)
x, y = Consts("x y", Element)
xs = Const("xs", List)
member = Function("ADT.Member", Element, List, BoolSort())
member_clauses = (
    And(xs.is_Cons, x == xs.head),
    And(xs.is_Cons, member(x, xs.tail)),
)
member_operator = relation_operator(member, [x, xs], *member_clauses)
member = define_least(member, [x, xs], *member_clauses)
member_induct = least_induct(member_operator)
member_conditional = least_unfold(member_operator)
member_unfold = member_conditional(prove(member_conditional.thm.arg(0)))
member_invariant = member_induct(Lambda([x, xs], xs != List.Nil))
member_nonempty = member_invariant(prove(member_invariant.thm.arg(0)))

pf = Lemma(member(x, List.Cons(y, List.Cons(x, List.Nil))))
pf.unfold(member)
pf.fix()
closed = pf.intro()
pf.specialize(closed, x, List.Cons(x, List.Nil), keep=True)
pf.specialize(closed, x, List.Cons(y, List.Cons(x, List.Nil)), keep=True)
pf.auto()
member_tail = pf.qed()

pf = Lemma(Not(member(x, List.Nil)))
h = pf.intro()
pf.unfold(member, at=h)
pf.specialize(pf.top_goal().ctx[-1], Lambda([x, xs], xs != List.Nil))
pf.auto()
member_nil = pf.qed()

if __name__ == "__main__":
    print(even_two)
    print(not_even_one)
    print(member_tail)
    print(member_nil)
