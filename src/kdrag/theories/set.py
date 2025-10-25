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
    |= ForAll([A, B], union(A, B) == union(B, A))
    """
    S = smt.SetSort(T)
    smt.sort_registry[S.get_id()] = S
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

    S.compl_invol = kd.prove(smt.ForAll([A], ~~A == A))
    S.compl_empty = kd.prove(~S.empty == S.full)
    S.compl_full = kd.prove(~S.full == S.empty)
    S.DeM_union = kd.prove(smt.ForAll([A, B], ~(A | B) == ~A & ~B))
    S.DeM_inter = kd.prove(smt.ForAll([A, B], ~(A & B) == ~A | ~B))
    S.diff_as_inter = kd.prove(smt.ForAll([A, B], A - B == A & ~B))

    S.absorp_or = kd.prove(smt.ForAll([A, B], A | (A & B) == A))
    S.absorp_and = kd.prove(smt.ForAll([A, B], A & (A | B) == A))

    S.dist_and_over_or = kd.prove(
        smt.ForAll([A, B, C], A & (B | C) == (A & B) | (A & C))
    )

    S.dist_or_over_and = kd.prove(
        smt.ForAll([A, B, C], A | (B & C) == (A | B) & (A | C))
    )

    S.sub_refl = kd.prove(smt.ForAll([A], A <= A))
    S.sub_trans = kd.prove(
        smt.ForAll([A, B, C], smt.Implies((A <= B) & (B <= C), (A <= C)))
    )
    S.sub_antisym = kd.prove(
        smt.ForAll([A, B], smt.Implies((A <= B) & (B <= A), (A == B)))
    )

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
    |= setminus(A, A) == K(Int, False)
    """
    return smt.SetDifference(A, B)


def subset(A: smt.ArrayRef, B: smt.ArrayRef) -> smt.BoolRef:
    """
    >>> IntSet = Set(smt.IntSort())
    >>> A = smt.Const("A", IntSet)
    >>> kd.prove(subset(IntSet.empty, A))
    |= subset(K(Int, False), A)
    >>> kd.prove(subset(A, A))
    |= subset(A, A)
    >>> kd.prove(subset(A, IntSet.full))
    |= subset(A, K(Int, True))
    """
    return smt.IsSubset(A, B)


def complement(A: smt.ArrayRef) -> smt.ArrayRef:
    """
    Complement of a set.
    >>> IntSet = Set(smt.IntSort())
    >>> A = smt.Const("A", IntSet)
    >>> kd.prove(complement(complement(A)) == A)
    |= complement(complement(A)) == A
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
    #|= SetHasSize(empty, 0)
    
    return smt.SetHasSize(A, n)
"""


def Singleton(x: smt.ExprRef) -> smt.ArrayRef:
    """
    >>> x = smt.Int("x")
    >>> kd.prove(Singleton(smt.IntVal(3))[3])
    |= Store(K(Int, False), 3, True)[3]
    >>> kd.prove(smt.Not(Singleton(smt.IntVal(3))[4]))
    |= Not(Store(K(Int, False), 3, True)[4])
    """
    return smt.Store(smt.EmptySet(x.sort()), x, smt.BoolVal(True))


def PowerSet(A: smt.ArrayRef) -> smt.ArrayRef:
    """
    Power set of A : Set( Set(T) )
    >>> IntSet = Set(smt.IntSort())
    >>> A = Singleton(smt.IntVal(3))
    >>> P = PowerSet(A)
    >>> kd.prove(member(IntSet.empty, P))
    |= Lambda(c!..., subset(c!..., Store(K(Int, False), 3, True)))[K(Int,
        False)]
    """
    B = smt.FreshConst(A.sort())
    return smt.Lambda([B], B <= A)


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


@functools.cache
def bigunion(T: smt.SortRef) -> smt.FuncDeclRef:
    """
    Abstracted bigunion
    """
    A = smt.Const("A", Set(Set(T)))
    return kd.define("bigunion", [A], BigUnion(A))


def FamilyUnion(family: smt.ArrayRef) -> smt.ArrayRef:
    """
    Countable union of a sequence of sets `Int -> A -> Bool`.

    >>> ISet = Set(smt.IntSort())
    >>> i,j,k = smt.Ints("i j k")
    >>> kd.prove(smt.ForAll([k], FamilyUnion(smt.Lambda([i], smt.Lambda([j], i == j)))[k]))
        |= ForAll(k,
           Lambda(x!...,
                  Exists(i!...,
                         Lambda(i, Lambda(j, i == j))[i!...][x!...]))[k])
    """
    sort = family.sort()
    I = sort.domain()
    S = sort.range()
    assert S.range() == smt.BoolSort()
    x = smt.FreshConst(S.domain(), prefix="x")
    i = smt.FreshConst(I, prefix="i")
    return smt.Lambda([x], smt.Exists([i], family[i][x]))


def CountInter(seq: smt.ArrayRef) -> smt.ArrayRef:
    """
    Countable intersection of a sequence of sets `Int -> A -> Bool`.

    >>> ISet = Set(smt.IntSort())
    >>> i,j,k = smt.Ints("i j k")
    >>> kd.prove(smt.ForAll([k], smt.Not(CountInter(smt.Lambda([i], smt.Lambda([j], i == j)))[k])))
    |= ForAll(k,
           Not(Lambda(x!...,
                      ForAll(i!...,
                             Lambda(i, Lambda(j, i == j))[i!...][x!...]))[k]))
    """
    sort = seq.sort()
    assert sort.domain() == smt.IntSort()
    S = sort.range()
    assert S.range() == smt.BoolSort()
    x = smt.FreshConst(S.domain(), prefix="x")
    i = smt.FreshInt(prefix="i")
    return smt.Lambda([x], smt.ForAll([i], seq[i][x]))


def Surjective(f: smt.FuncDeclRef) -> smt.BoolRef:
    """
    A surjective function maps to every possible value in the range.

    >>> x = smt.Int("x")
    >>> neg = (-x).decl()
    >>> kd.prove(Surjective(neg))
    |= ForAll(y!..., Lambda(y, Exists(x0, -x0 == y))[y!...])
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
    |= ForAll([x!..., y!...],
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
    |= Exists(finwit!...,
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
    # Lambda form?
    # return A == smt.Lambda([x], smt.Contains(finwit(A), smt.Unit(x))


RSet = Set(smt.RealSort())
IntSet = Set(smt.IntSort())
BoolSet = Set(smt.BoolSort())
# TODO: Theorems: Finite is closed under most operations

# @functools.cache
# def FinSet(T : smt.SortRef) -> smt.DatatypeRef:
#    return NewType("FinSet_" + str(T), T, pred=Finite)


def EClass(x: smt.ExprRef, eqrel) -> smt.QuantifierRef:
    """
    Equivalence class [x] under equivalence relation eqrel.
    The set of all v such that eqrel(x, v) holds.
    https://en.wikipedia.org/wiki/Equivalence_class

    >>> x,y = smt.Ints("x y")
    >>> (A := EClass(x, lambda a,b: a % 3 == b % 3))
    Lambda(v!..., x%3 == v!...%3)
    >>> kd.prove(EClass(3, lambda a,b: a % 3 == b % 3)[3])
    |= Lambda(v!..., 3%3 == v!...%3)[3]

    """
    x = smt._py2expr(x)
    v = smt.FreshConst(x.sort(), prefix="v")
    return smt.Lambda([v], eqrel(x, v))


def Quot(dom: smt.SortRef, eqrel) -> smt.QuantifierRef:
    """
    Quotient space under equivalence relation eqrel.
    A set of sets of A.
    The set of equivalence classes
    https://en.wikipedia.org/wiki/Equivalence_class

    >>> x = smt.Int("x")
    >>> l = kd.Lemma((smt.IntSort() // (lambda a,b: a % 3 == b % 3))[EClass(x, lambda a,b: a % 3 == b % 3)])
    >>> l.simp().exists(x).auto()
    Nothing to do. Hooray!
    >>> _ = l.qed()
    """
    # TODO: consider supporting ArrayRef too as first argument
    x = smt.FreshConst(dom, prefix="x")
    A = smt.FreshConst(smt.SetSort(dom), prefix="A")
    return smt.Lambda([A], smt.Exists([x], A == EClass(x, eqrel)))


smt.SortRef.__floordiv__ = Quot  # type: ignore


def Choose(A: smt.FuncRef, auto=False) -> tuple[list[smt.ExprRef], kd.Proof]:
    """
    Choose an arbitrary element from set A.

    >>> x = smt.Int("x")
    >>> Choose(smt.Lambda([x], x > 0))
    ([c!...], |= Implies(Exists(c!..., c!... > 0), c!... > 0))
    """
    # TODO: maybe discharge the existential too?
    xs = [smt.FreshConst(sort) for sort in smt.domains(A)]
    return kd.kernel.obtain(smt.Exists(xs, A(*xs)))
