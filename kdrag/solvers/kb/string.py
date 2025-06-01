"""

See https://www.philipzucker.com/string_knuth/
"""

from typing import Optional, Sequence


def subseq(s: Sequence, t: Sequence) -> Optional[int]:
    """Return index when s is a subsequence of t, None otherwise

    >>> subseq("abc", "abacabadabacaba") is None
    True
    >>> subseq("abc", "abacabc")
    4
    """
    for i in range(len(t) - len(s) + 1):
        if s == t[i : i + len(s)]:
            return i
    return None


def replace(s: tuple, lhs: tuple, rhs: tuple) -> tuple:
    """
    Find and replace the first occurrence of lhs in s with rhs.

    >>> replace((1,2,3,4), (2,3), (5,6))
    (1, 5, 6, 4)
    >>> replace((1,2,3,4), (2,3), (5,6,7))
    (1, 5, 6, 7, 4)
    >>> replace((1,2,3,4), (2,3), (5,6,7,8))
    (1, 5, 6, 7, 8, 4)
    >>> replace((1,1), (4,4), (2,2))
    (1, 1)
    """
    i = subseq(lhs, s)
    if i is not None:
        return s[:i] + rhs + s[i + len(lhs) :]
    else:
        return s


def rewrite(s, R, exclude=-1):
    """
    Rewrite to a fixed point using rules R.

    Exclude is useful for simplifying a rule

    >>> rewrite((1,2,3,4), [((2,3), (5,6)), ((5,6), (7,8))])
    (1, 7, 8, 4)
    >>> rewrite((1,1,1,1,1,1), [((1,1), ())])
    ()
    >>> rewrite((1,1,1,1,2,1), [((1,1), ())])
    (2, 1)
    """
    while True:
        s0 = s
        for i, (lhs, rhs) in enumerate(R):
            if i != exclude:
                s = replace(s, lhs, rhs)
        if s == s0:
            return s


def shortlex_swap(s, t):
    """
    Order by length, then tie break by contents lexicographically.
    Returns a tuple (s', t') where t' is the "shorter" or "smaller" of the two.
    Asserts False if s and t are equal.

    >>> shortlex_swap((1,2,3), (0,0))
    ((1, 2, 3), (0, 0))
    >>> shortlex_swap((1,2,3), (1,2,4))
    ((1, 2, 4), (1, 2, 3))
    """
    if len(s) < len(t):
        return t, s
    elif len(s) > len(t):
        return s, t
    elif s < t:
        return t, s
    elif s > t:
        return s, t
    else:
        assert False


def overlaps(s, t):
    """
    critical pairs https://en.wikipedia.org/wiki/Critical_pair_(term_rewriting)

    >>> assert set(overlaps((1,2), (2,3))) == {(1,2,3)}
    >>> assert set(overlaps((1,2), (3,2))) == set()
    >>> assert set(overlaps((1,2), (2,1))) == {(1,2,1), (2,1,2)}
    >>> assert set(overlaps((1,2), (1,2))) == {(1,2)}
    >>> assert set(overlaps((2,2), (2,2,3))) == {(2,2,3), (2,2,2,3)}
    >>> assert set(overlaps((), (1,2))) == {(1,2)}
    """
    # make len(t) >= len(s)
    if len(t) < len(s):
        s, t = t, s
    if subseq(s, t) is not None:
        yield t
    # iterate over possible overlap sizes 1 to the len(s) at edges
    for osize in range(1, len(s)):
        if t[-osize:] == s[:osize]:
            yield t + s[osize:]
        if s[-osize:] == t[:osize]:
            yield s + t[osize:]


def deduce(R):
    """deduce all possible critical pairs from R"""
    for i, (lhs, rhs) in enumerate(R):
        for j in range(i):
            lhs1, rhs1 = R[j]
            for o in overlaps(lhs1, lhs):
                x, y = rewrite(o, [(lhs1, rhs1)]), rewrite(o, [(lhs, rhs)])
                if x != y:
                    yield x, y


def KB(E):
    """
    String Knuth-Bendix completion algorithm.

    >>> e = 0
    >>> a = 1 # a is rotate square
    >>> b = 2 # b is flip square horizontally.
    >>> E = [\
        ((-a, a), ()),\
        ((-b,b), ()),\
        ((a,a,a,a), ()),\
        ((b,b), ()),\
        ((a,a,a,b), (b,a))\
        ]
    >>> R = KB(E)
    >>> E,R = simplify(R)
    """
    E = E.copy()
    R = []
    done = False
    while not done:
        done = True
        E.extend(deduce(R))
        while E:
            lhs, rhs = E.pop()
            lhs, rhs = rewrite(lhs, R), rewrite(rhs, R)
            if lhs != rhs:
                done = False
                lhs, rhs = shortlex_swap(lhs, rhs)
                R.append((lhs, rhs))

    return R


def simplify(R):
    Rnew = []
    E = []
    for i, (lhs, rhs) in enumerate(R):
        # lhs = reduce(Rnew)
        lhs1 = rewrite(
            lhs, R, exclude=i
        )  # L-simplify. nebulous correctness. I might be playing it both ways here. I keep around the old R even though I should have moved it to E?
        rhs1 = rewrite(rhs, R)  # R-simplify
        if lhs1 == lhs:
            Rnew.append((lhs, rhs1))
        elif lhs1 != rhs1:
            E.append((lhs1, rhs1))
    return E, Rnew
