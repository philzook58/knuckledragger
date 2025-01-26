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

    return S


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
