"""Inductive relations on ADTs, with a callable wrapper and named proofs.

Run: PYTHONPATH=src python examples/indrel_adt.py
"""

from kdrag import Nat, ListSort, Theorem, indrel, prove
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
even = indrel(even, n, n == Nat.Z, Exists(m, And(n == Nat.S(Nat.S(m)), even(m))))
even_invariant = even.induct(Lambda(n, n != Nat.S(Nat.Z)))
even_excludes_one = even_invariant(prove(even_invariant.thm.arg(0)))


@Theorem(even(Nat.S(Nat.S(Nat.Z))))
def even_two(pf):
    pf.auto(by=[even.unfold(Nat.Z), even.unfold(Nat.S(Nat.S(Nat.Z)))])


@Theorem(Not(even(Nat.S(Nat.Z))))
def not_even_one(pf):
    pf.auto(by=[even_excludes_one])


# Member(x, Cons(x, xs)); Member(x, xs) -> Member(x, Cons(y, xs)).
Element = DeclareSort("ADT.Member.Element")
List = ListSort(Element)
x, y = Consts("x y", Element)
xs = Const("xs", List)
member = Function("ADT.Member", Element, List, BoolSort())
member = indrel(
    member, [x, xs], And(xs.is_Cons, x == xs.head), And(xs.is_Cons, member(x, xs.tail))
)
member_invariant = member.induct(Lambda([x, xs], xs != List.Nil))
member_nonempty = member_invariant(prove(member_invariant.thm.arg(0)))


@Theorem(member(x, List.Cons(y, List.Cons(x, List.Nil))))
def member_tail(pf):
    pf.auto(
        by=[
            member.unfold(x, List.Cons(x, List.Nil)),
            member.unfold(x, List.Cons(y, List.Cons(x, List.Nil))),
        ]
    )


@Theorem(Not(member(x, List.Nil)))
def member_nil(pf):
    pf.auto(by=[member_nonempty])


if __name__ == "__main__":
    print(even_two)
    print(not_even_one)
    print(member_tail)
    print(member_nil)
