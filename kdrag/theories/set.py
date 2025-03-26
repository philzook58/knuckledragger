"""
First class sets ArraySort(T, Bool)
"""

import kdrag as kd
import kdrag.smt as smt
import functools


@functools.cache
def Set(T):
    """
    Sets of elements of sort T.
    This registers a number of helper notations and useful lemmas.

    >>> IntSet = Set(smt.IntSort())
    >>> IntSet.empty
    K(Int, False)
    >>> IntSet.full
    K(Int, True)
    >>> A,B = smt.Consts("A B", IntSet)
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
    |- ForAll([A, B], union(A, B) == union(B, A))
    """
    S = smt.SetSort(T)
    S.empty = smt.EmptySet(T)
    S.full = smt.FullSet(T)
    kd.notation.and_.register(S, smt.SetIntersect)
    kd.notation.or_.register(S, smt.SetUnion)
    kd.notation.sub.register(S, smt.SetDifference)
    kd.notation.invert.register(S, smt.SetComplement)
    kd.notation.le.register(S, smt.IsSubset)
    kd.notation.lt.register(S, lambda x, y: smt.And(smt.IsSubset(x, y), x != y))
    kd.notation.ge.register(S, lambda x, y: smt.IsSubset(y, x))

    A, B, C = smt.Consts("A B C", S)

    # https://en.wikipedia.org/wiki/List_of_set_identities_and_relations

    S.union_comm = kd.prove(smt.ForAll([A, B], A | B == B | A))
    S.union_assoc = kd.prove(smt.ForAll([A, B, C], (A | B) | C == A | (B | C)))
    S.union_empty = kd.prove(smt.ForAll([A], A | S.empty == A))
    S.union_full = kd.prove(smt.ForAll([A], A | S.full == S.full))
    S.union_self = kd.prove(smt.ForAll([A], A | A == A))

    S.inter_comm = kd.prove(smt.ForAll([A, B], A & B == B & A))
    S.inter_assoc = kd.prove(smt.ForAll([A, B, C], (A & B) & C == A & (B & C)))
    S.inter_empty = kd.prove(smt.ForAll([A], A & S.empty == S.empty))
    S.inter_full = kd.prove(smt.ForAll([A], A & S.full == A))
    S.inter_self = kd.prove(smt.ForAll([A], A & A == A))

    S.diff_empty = kd.prove(smt.ForAll([A], A - S.empty == A))
    S.diff_full = kd.prove(smt.ForAll([A], A - S.full == S.empty))
    S.diff_self = kd.prove(smt.ForAll([A], A - A == S.empty))

    S.finite = kd.define("finite", [A], Finite(A))

    return S


def is_set(A: smt.ArrayRef) -> bool:
    return isinstance(A.sort(), smt.ArraySortRef) and A.sort().range() == smt.BoolSort()


def union(A: smt.ArrayRef, B: smt.ArrayRef) -> smt.ArrayRef:
    return smt.SetUnion(A, B)


def inter(A: smt.ArrayRef, B: smt.ArrayRef) -> smt.ArrayRef:
    return smt.SetIntersect(A, B)


def diff(A: smt.ArrayRef, B: smt.ArrayRef) -> smt.ArrayRef:
    """
    Set difference.
    >>> IntSet = Set(smt.IntSort())
    >>> A = smt.Const("A", IntSet)
    >>> kd.prove(diff(A, A) == IntSet.empty)
    |- setminus(A, A) == K(Int, False)
    """
    return smt.SetDifference(A, B)


def subset(A: smt.ArrayRef, B: smt.ArrayRef) -> smt.BoolRef:
    """
    >>> IntSet = Set(smt.IntSort())
    >>> A = smt.Const("A", IntSet)
    >>> kd.prove(subset(IntSet.empty, A))
    |- subset(K(Int, False), A)
    >>> kd.prove(subset(A, A))
    |- subset(A, A)
    >>> kd.prove(subset(A, IntSet.full))
    |- subset(A, K(Int, True))
    """
    return smt.IsSubset(A, B)


def complement(A: smt.ArrayRef) -> smt.ArrayRef:
    """
    Complement of a set.
    >>> IntSet = Set(smt.IntSort())
    >>> A = smt.Const("A", IntSet)
    >>> kd.prove(complement(complement(A)) == A)
    |- complement(complement(A)) == A
    """
    return smt.SetComplement(A)


def member(x: smt.ExprRef, A: smt.ArrayRef) -> smt.BoolRef:
    """
    >>> x = smt.Int("x")
    >>> A = smt.Const("A", Set(smt.IntSort()))
    >>> member(x, A)
    A[x]
    """
    return smt.IsMember(x, A)


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
    #|- SetHasSize(empty, 0)
    
    return smt.SetHasSize(A, n)
"""


def Range(f: smt.FuncDeclRef) -> smt.ArrayRef:
    """
    Range of a function. Also known as the Image of the function.

    >>> f = smt.Function("f", smt.IntSort(), smt.IntSort())
    >>> Range(f)
    Lambda(y, Exists(x0, f(x0) == y))
    """
    xs = [smt.Const("x" + str(i), f.domain(i)) for i in range(f.arity())]
    y = smt.Const("y", f.range())
    return smt.Lambda([y], kd.QExists(xs, f(*xs) == y))


def BigUnion(A: smt.ArrayRef) -> smt.ArrayRef:
    """
    Big union of a set of sets.
    >>> IntSet = Set(smt.IntSort())
    >>> A = smt.Const("A", Set(IntSet))
    >>> BigUnion(A)
    Lambda(x, Exists(B, And(B[x], A[B])))
    """
    assert is_set(A)
    sort = A.sort().domain()
    B = smt.Const("B", sort)
    assert is_set(B)
    x = smt.Const("x", sort.domain())
    return smt.Lambda([x], kd.QExists([B], B[x], A[B]))


def Surjective(f: smt.FuncDeclRef) -> smt.BoolRef:
    """
    A surjective function maps to every possible value in the range.

    >>> x = smt.Int("x")
    >>> neg = (-x).decl()
    >>> kd.prove(Surjective(neg))
    |- ForAll(y!..., Lambda(y, Exists(x0, -x0 == y))[y!...])
    """
    # TODO: also support ArrayRef
    # TODO: I need to be consistent on whether I need FreshConst here or not.
    y = smt.FreshConst(f.range(), prefix="y")
    return kd.QForAll([y], smt.IsMember(y, Range(f)))


def Injective(f: smt.FuncDeclRef) -> smt.BoolRef:
    """
    An injective function maps distinct inputs to distinct outputs.

    >>> x, y = smt.Ints("x y")
    >>> neg = (-x).decl()
    >>> kd.prove(Injective(neg))
    |- ForAll([x!..., y!...],
           Implies(-x!... == -y!..., x!... == y!...))
    """
    xs1 = [smt.FreshConst(f.domain(i), prefix="x") for i in range(f.arity())]
    xs2 = [smt.FreshConst(f.domain(i), prefix="y") for i in range(f.arity())]
    if len(xs1) == 1:
        conc = xs1[0] == xs2[0]
    else:
        conc = smt.And(*[x1 == x2 for x1, x2 in zip(xs1, xs2)])
    return kd.QForAll(xs1 + xs2, smt.Implies(f(*xs1) == f(*xs2), conc))


def Finite(A: smt.ArrayRef) -> smt.BoolRef:
    """
    A set is finite if it has a finite number of elements.

    See https://cvc5.github.io/docs/cvc5-1.1.2/theories/sets-and-relations.html#finite-sets

    >>> IntSet = Set(smt.IntSort())
    >>> kd.prove(Finite(IntSet.empty))
    |- Exists(finwit!...,
           ForAll(x!...,
                  K(Int, False)[x!...] ==
                  Contains(finwit!..., Unit(x!...))))
    """
    dom = A.sort().domain()
    x = smt.FreshConst(dom, prefix="x")
    finwit = smt.FreshConst(smt.SeqSort(A.domain()), prefix="finwit")
    return kd.QExists(
        [finwit], kd.QForAll([x], A[x] == smt.Contains(finwit, smt.Unit(x)))
    )


# TODO: Theorems: Finite is closed under most operations

# @functools.cache
# def FinSet(T : smt.SortRef) -> smt.DatatypeRef:
#    return NewType("FinSet_" + str(T), T, pred=Finite)
