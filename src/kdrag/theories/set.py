"""
First class sets ArraySort(T, Bool)
"""

import kdrag as kd
from kdrag import Lemma, QExists, QForAll, define, prove  # noqa: F401
import kdrag.smt as smt
from kdrag.smt import (  # noqa: F401
    And,
    BoolSort,
    BoolVal,
    Const,
    Consts,
    Contains,
    EmptySet,
    Exists,
    ForAll,
    FreshConst,
    FreshInt,
    FullSet,
    Function,
    Implies,
    Int,
    IntSort,
    IntVal,
    Ints,
    IsMember,
    IsSubset,
    Lambda,
    Not,
    RealSort,
    SeqSort,
    SetComplement,
    SetDifference,
    SetIntersect,
    SetSort,
    SetUnion,
    Store,
    Unit,
    domains,
)
import functools


@functools.cache
def Set(T):
    """
    Sets of elements of sort T.
    This registers a number of helper notations and useful lemmas.

    >>> IntSet = Set(IntSort())
    >>> IntSet.empty
    K(Int, False)
    >>> IntSet.full
    K(Int, True)
    >>> A,B = Consts("A B", IntSet)
    >>> A & B
    intersection(A, B)
    >>> A | B
    union(A, B)
    >>> A - B
    setminus(A, B)
    >>> A <= B
    subset(A, B)
    >>> A < B
    And(subset(A, B), A != B)
    >>> A >= B
    subset(B, A)
    >>> IntSet.union_comm
    |= ForAll([A, B], union(A, B) == union(B, A))
    """
    S = SetSort(T)
    smt.sort_registry[S.get_id()] = S
    S.empty = EmptySet(T)
    S.full = FullSet(T)
    kd.notation.sub.register(S, SetDifference)
    kd.notation.and_.register(S, SetIntersect)
    kd.notation.or_.register(S, SetUnion)

    kd.notation.invert.register(S, SetComplement)
    kd.notation.le.register(S, IsSubset)
    kd.notation.lt.register(S, lambda x, y: And(IsSubset(x, y), x != y))
    kd.notation.ge.register(S, lambda x, y: IsSubset(y, x))

    A, B, C = Consts("A B C", S)

    # https://en.wikipedia.org/wiki/List_of_set_identities_and_relations

    S.union_comm = prove(ForAll([A, B], A | B == B | A))
    S.union_assoc = prove(ForAll([A, B, C], (A | B) | C == A | (B | C)))
    S.union_empty = prove(ForAll([A], A | S.empty == A))
    S.union_full = prove(ForAll([A], A | S.full == S.full))
    S.union_self = prove(ForAll([A], A | A == A))

    S.inter_comm = prove(ForAll([A, B], A & B == B & A))
    S.inter_assoc = prove(ForAll([A, B, C], (A & B) & C == A & (B & C)))
    S.inter_empty = prove(ForAll([A], A & S.empty == S.empty))
    S.inter_full = prove(ForAll([A], A & S.full == A))
    S.inter_self = prove(ForAll([A], A & A == A))

    S.diff_empty = prove(ForAll([A], A - S.empty == A))
    S.diff_full = prove(ForAll([A], A - S.full == S.empty))
    S.diff_self = prove(ForAll([A], A - A == S.empty))

    S.finite = finite_decl(S)  # kd.define("finite", [A], Finite(A))

    S.compl_invol = prove(ForAll([A], ~~A == A))
    S.compl_empty = prove(~S.empty == S.full)
    S.compl_full = prove(~S.full == S.empty)
    S.DeM_union = prove(ForAll([A, B], ~(A | B) == ~A & ~B))
    S.DeM_inter = prove(ForAll([A, B], ~(A & B) == ~A | ~B))
    S.diff_as_inter = prove(ForAll([A, B], A - B == A & ~B))

    S.absorp_or = prove(ForAll([A, B], A | (A & B) == A))
    S.absorp_and = prove(ForAll([A, B], A & (A | B) == A))

    S.dist_and_over_or = prove(ForAll([A, B, C], A & (B | C) == (A & B) | (A & C)))

    S.dist_or_over_and = prove(ForAll([A, B, C], A | (B & C) == (A | B) & (A | C)))

    S.sub_refl = prove(ForAll([A], A <= A))
    S.sub_trans = prove(ForAll([A, B, C], Implies((A <= B) & (B <= C), (A <= C))))
    S.sub_antisym = prove(ForAll([A, B], Implies((A <= B) & (B <= A), (A == B))))

    return S


def is_set(A: smt.ArrayRef) -> bool:
    return isinstance(A.sort(), smt.ArraySortRef) and A.sort().range() == BoolSort()


def union(A: smt.ArrayRef, B: smt.ArrayRef) -> smt.ArrayRef:
    return SetUnion(A, B)


def inter(A: smt.ArrayRef, B: smt.ArrayRef) -> smt.ArrayRef:
    return SetIntersect(A, B)


def diff(A: smt.ArrayRef, B: smt.ArrayRef) -> smt.ArrayRef:
    """
    Set difference.
    >>> IntSet = Set(IntSort())
    >>> A = Const("A", IntSet)
    >>> prove(diff(A, A) == IntSet.empty)
    |= setminus(A, A) == K(Int, False)
    """
    return SetDifference(A, B)


def subset(A: smt.ArrayRef, B: smt.ArrayRef) -> smt.BoolRef:
    """
    >>> IntSet = Set(IntSort())
    >>> A = Const("A", IntSet)
    >>> prove(subset(IntSet.empty, A))
    |= subset(K(Int, False), A)
    >>> prove(subset(A, A))
    |= subset(A, A)
    >>> prove(subset(A, IntSet.full))
    |= subset(A, K(Int, True))
    """
    return IsSubset(A, B)


def complement(A: smt.ArrayRef) -> smt.ArrayRef:
    """
    Complement of a set.
    >>> IntSet = Set(IntSort())
    >>> A = Const("A", IntSet)
    >>> prove(complement(complement(A)) == A)
    |= complement(complement(A)) == A
    """
    return SetComplement(A)


def member(x: smt.ExprRef, A: smt.ArrayRef) -> smt.BoolRef:
    """
    >>> x = Int("x")
    >>> A = Const("A", Set(IntSort()))
    >>> member(x, A)
    A[x]
    """
    return IsMember(x, A)


"""
# unsupported. :(
# https://github.com/Z3Prover/z3/issues/6788
def has_size(A: smt.ArrayRef, n: smt.ArithRef) -> smt.BoolRef:

    #>>> IntSet = Set(smt.IntSort())
    #>>> A = smt.Const("A", IntSet)
    #>>> n = smt.Int("n")
    #>>> has_size(A, n)
    #SetHasSize(A, n)
    #>>> kd.prove(has_size(IntSet.empty, 0))
    #|= SetHasSize(empty, 0)
    
    return smt.SetHasSize(A, n)
"""


def Singleton(x: smt.ExprRef) -> smt.ArrayRef:
    """
    >>> x = Int("x")
    >>> prove(Singleton(IntVal(3))[3])
    |= Store(K(Int, False), 3, True)[3]
    >>> prove(Not(Singleton(IntVal(3))[4]))
    |= Not(Store(K(Int, False), 3, True)[4])
    """
    return Store(EmptySet(x.sort()), x, BoolVal(True))


def PowerSet(A: smt.ArrayRef) -> smt.ArrayRef:
    """
    Power set of A : Set( Set(T) )
    >>> IntSet = Set(IntSort())
    >>> A = Singleton(IntVal(3))
    >>> P = PowerSet(A)
    >>> prove(member(IntSet.empty, P))
    |= Lambda(c!..., subset(c!..., Store(K(Int, False), 3, True)))[K(Int,
        False)]
    """
    B = FreshConst(A.sort())
    return Lambda([B], B <= A)


def Range(f: smt.FuncDeclRef) -> smt.ArrayRef:
    """
    Range of a function. Also known as the Image of the function.

    >>> f = Function("f", IntSort(), IntSort())
    >>> Range(f)
    Lambda(y, Exists(x0, f(x0) == y))
    """
    xs = [Const("x" + str(i), f.domain(i)) for i in range(f.arity())]
    y = Const("y", f.range())
    return Lambda([y], QExists(xs, f(*xs) == y))


def BigUnion(A: smt.ArrayRef) -> smt.ArrayRef:
    """
    Big union of a set of sets.
    >>> IntSet = Set(IntSort())
    >>> A = Const("A", Set(IntSet))
    >>> BigUnion(A)
    Lambda(x, Exists(B, And(B[x], A[B])))
    """
    assert is_set(A)
    sort = A.sort().domain()
    B = Const("B", sort)
    assert is_set(B)
    x = Const("x", sort.domain())
    return Lambda([x], QExists([B], B[x], A[B]))


@functools.cache
def bigunion(T: smt.SortRef) -> smt.FuncDeclRef:
    """
    Abstracted bigunion
    """
    A = Const("A", Set(Set(T)))
    return define("bigunion", [A], BigUnion(A))


def FamilyUnion(family: smt.ArrayRef) -> smt.ArrayRef:
    """
    Countable union of a sequence of sets `Int -> A -> Bool`.

    >>> ISet = Set(IntSort())
    >>> i,j,k = Ints("i j k")
    >>> prove(ForAll([k], FamilyUnion(Lambda([i], Lambda([j], i == j)))[k]))
        |= ForAll(k,
           Lambda(x!...,
                  Exists(i!...,
                         Lambda(i, Lambda(j, i == j))[i!...][x!...]))[k])
    """
    sort = family.sort()
    I = sort.domain()
    S = sort.range()
    assert S.range() == BoolSort()
    x = FreshConst(S.domain(), prefix="x")
    i = FreshConst(I, prefix="i")
    return Lambda([x], Exists([i], family[i][x]))


def CountInter(seq: smt.ArrayRef) -> smt.ArrayRef:
    """
    Countable intersection of a sequence of sets `Int -> A -> Bool`.

    >>> ISet = Set(IntSort())
    >>> i,j,k = Ints("i j k")
    >>> prove(ForAll([k], Not(CountInter(Lambda([i], Lambda([j], i == j)))[k])))
    |= ForAll(k,
           Not(Lambda(x!...,
                      ForAll(i!...,
                             Lambda(i, Lambda(j, i == j))[i!...][x!...]))[k]))
    """
    sort = seq.sort()
    assert sort.domain() == IntSort()
    S = sort.range()
    assert S.range() == BoolSort()
    x = FreshConst(S.domain(), prefix="x")
    i = FreshInt(prefix="i")
    return Lambda([x], ForAll([i], seq[i][x]))


def Surjective(f: smt.FuncDeclRef) -> smt.BoolRef:
    """
    A surjective function maps to every possible value in the range.

    >>> x = Int("x")
    >>> neg = (-x).decl()
    >>> prove(Surjective(neg))
    |= ForAll(y!..., Lambda(y, Exists(x0, -x0 == y))[y!...])
    """
    # TODO: also support ArrayRef
    # TODO: I need to be consistent on whether I need FreshConst here or not.
    y = FreshConst(f.range(), prefix="y")
    return QForAll([y], IsMember(y, Range(f)))


def Injective(f: smt.FuncDeclRef) -> smt.BoolRef:
    """
    An injective function maps distinct inputs to distinct outputs.

    >>> x, y = Ints("x y")
    >>> neg = (-x).decl()
    >>> prove(Injective(neg))
    |= ForAll([x!..., y!...],
           Implies(-x!... == -y!..., x!... == y!...))
    """
    xs1 = [FreshConst(f.domain(i), prefix="x") for i in range(f.arity())]
    xs2 = [FreshConst(f.domain(i), prefix="y") for i in range(f.arity())]
    if len(xs1) == 1:
        conc = xs1[0] == xs2[0]
    else:
        conc = And(*[x1 == x2 for x1, x2 in zip(xs1, xs2)])
    return QForAll(xs1 + xs2, Implies(f(*xs1) == f(*xs2), conc))


def Finite(A: smt.ArrayRef) -> smt.BoolRef:
    """
    A set is finite if it has a finite number of elements.

    See:
    - https://cvc5.github.io/docs/cvc5-1.1.2/theories/sets-and-relations.html#finite-sets
    - https://isabelle.in.tum.de/library/HOL/HOL-Library/FSet.html

    >>> IntSet = Set(IntSort())
    >>> prove(Finite(IntSet.empty))
    |= Exists(finwit!...,
           ForAll(x!...,
                  K(Int, False)[x!...] ==
                  Contains(finwit!..., Unit(x!...))))
    """
    dom = A.sort().domain()
    x = FreshConst(dom, prefix="x")
    finwit = FreshConst(SeqSort(A.domain()), prefix="finwit")
    return QExists([finwit], QForAll([x], A[x] == Contains(finwit, Unit(x))))
    # Lambda form?
    # return A == smt.Lambda([x], smt.Contains(finwit(A), smt.Unit(x))


@functools.cache
def finite_decl(T: smt.SortRef) -> smt.FuncDeclRef:
    """
    Abstracted finite predicate for sets of T.
    """
    A = Const("A", SetSort(T))
    return define(f"{T.sexpr()}.finite", [A], Finite(A))


def finite(A):
    doms = domains(A)
    assert len(doms) == 1
    return finite_decl(doms[0])(A)


@functools.cache
def finite_empty(T: smt.SortRef) -> kd.Proof:
    """
    Prove that the empty set is finite for sets of T.
    """
    return prove(finite(Set(T).empty), unfold=True)


RSet = Set(RealSort())
IntSet = Set(IntSort())
BoolSet = Set(BoolSort())
# TODO: Theorems: Finite is closed under most operations

# @functools.cache
# def FinSet(T : smt.SortRef) -> smt.DatatypeRef:
#    return NewType("FinSet_" + str(T), T, pred=Finite)


def EClass(x: smt.ExprRef, eqrel) -> smt.QuantifierRef:
    """
    Equivalence class [x] under equivalence relation eqrel.
    The set of all v such that eqrel(x, v) holds.
    https://en.wikipedia.org/wiki/Equivalence_class

    >>> x,y = Ints("x y")
    >>> (A := EClass(x, lambda a,b: a % 3 == b % 3))
    Lambda(v!..., x%3 == v!...%3)
    >>> prove(EClass(3, lambda a,b: a % 3 == b % 3)[3])
    |= Lambda(v!..., 3%3 == v!...%3)[3]

    """
    x = smt._py2expr(x)
    v = FreshConst(x.sort(), prefix="v")
    return Lambda([v], eqrel(x, v))


def Quot(dom: smt.SortRef, eqrel) -> smt.QuantifierRef:
    """
    Quotient space under equivalence relation eqrel.
    A set of sets of A.
    The set of equivalence classes
    https://en.wikipedia.org/wiki/Equivalence_class

    >>> x = Int("x")
    >>> l = Lemma((IntSort() // (lambda a,b: a % 3 == b % 3))[EClass(x, lambda a,b: a % 3 == b % 3)])
    >>> l.simp().exists(x).auto()
    Nothing to do. Hooray!
    >>> _ = l.qed()
    """
    # TODO: consider supporting ArrayRef too as first argument
    x = FreshConst(dom, prefix="x")
    A = FreshConst(SetSort(dom), prefix="A")
    return Lambda([A], Exists([x], A == EClass(x, eqrel)))


smt.SortRef.__floordiv__ = Quot  # type: ignore


def Choose(A: smt.FuncRef, auto=False) -> tuple[list[smt.ExprRef], kd.Proof]:
    """
    Choose an arbitrary element from set A.

    >>> x = Int("x")
    >>> Choose(Lambda([x], x > 0))
    ([c!...], |= Implies(Exists(c!..., c!... > 0), c!... > 0))
    """
    # TODO: maybe discharge the existential too?
    xs = [FreshConst(sort) for sort in domains(A)]
    return kd.kernel.obtain(Exists(xs, A(*xs)))


def Closed(S: smt.ArrayRef, f: smt.FuncDeclRef) -> smt.BoolRef:
    """
    A set S is closed under function f if for all x1,...,xn in S, f(x1,...,xn) is also in S.
    >>> x = Int("x")
    >>> prove(Closed(Lambda([x], x >= 0), (x + x).decl()))
    |= ForAll([x0!..., x1!...],
              Implies(And(x0!... >= 0, x1!... >= 0), x0!... + x1!... >= 0))
    """
    xs = [FreshConst(f.domain(i), prefix="x" + str(i)) for i in range(f.arity())]
    return QForAll(xs, *[S(x) for x in xs], S(f(*xs)))
