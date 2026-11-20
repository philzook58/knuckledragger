"""Inductive relations on ADTs, with a callable wrapper and named proofs.

Run: PYTHONPATH=src python examples/indrel_adt.py
"""

from kdrag import Nat, ListSort, Theorem, indrel
from kdrag.datatype import define_primrec
from kdrag.smt import (
    And,
    BoolSort,
    Const,
    Consts,
    DeclareSort,
    Exists,
    Function,
    ForAll,
    Lambda,
    Not,
)

# Even(0); Even(n) -> Even(S(S(n))).
n, m, k = Consts("n m k", Nat)
even = Function("ADT.Even", Nat, BoolSort())
even = indrel(even, n, n == Nat.Z, Exists(m, And(n == Nat.S(Nat.S(m)), even(m))))


double = define_primrec(
    "ADT.double", [n], Nat, Z=lambda: Nat.Z, S=lambda result: Nat.S(Nat.S(result))
)


@Theorem(ForAll(n, even(n), Exists(k, n == double(k))))
def even_is_double(pf):
    # Induct on the derivation of even(n), keeping an existential invariant.
    pf.specialize(even.induct, Lambda(n, Exists(k, n == double(k))))
    pf.beta(at=-1)
    pf.apply(-1)
    pf.fix()
    case = pf.intro()
    pf.split(at=case)
    # The recursive case supplies a witness k for the predecessor m.
    pf.obtain(-1)
    pf.split(at=-1)
    witness = pf.obtain(-1)
    pf.exists(Nat.S(witness))
    pf.auto(by=[double.defn(Nat.S(witness))])
    # Base case: zero is double zero.
    pf.exists(Nat.Z)
    pf.auto(by=[double.defn(Nat.Z)])


@Theorem(ForAll(n, even(n), n != Nat.S(Nat.Z)))
def even_excludes_one(pf):
    pf.specialize(even.induct, Lambda(n, n != Nat.S(Nat.Z)))
    pf.beta(at=-1)
    pf.apply(-1)
    pf.fix()
    pf.intro()
    pf.auto()


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


@Theorem(ForAll([x, xs], member(x, xs), xs != List.Nil))
def member_nonempty(pf):
    pf.specialize(member.induct, Lambda([x, xs], xs != List.Nil))
    pf.beta(at=-1)
    pf.apply(-1)
    pf.fixes()
    pf.intro()
    pf.auto()


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
    print(even_is_double)
    print(even_two)
    print(not_even_one)
    print(member_tail)
    print(member_nil)
