"""
Ground Multiset Rewriting and completion.

https://www.philipzucker.com/multiset_rw/
"""


def overlap(xs, ys):
    """Find minimal multiset that is a supermultiset of both xs and ys. Return None if this is just the union (trivial)"""
    nontriv = False
    res = []
    i, j = 0, 0
    while i < len(xs) and j < len(ys):
        x, n = xs[i]
        y, m = ys[j]
        if x < y:
            res.append((x, n))
            i += 1
        elif x > y:
            res.append((y, m))
            j += 1
        else:
            nontriv = True
            res.append((x, max(n, m)))
            i += 1
            j += 1
    if not nontriv:
        return None
    while i < len(xs):
        res.append(xs[i])
        i += 1
    while j < len(ys):
        res.append(ys[j])
        j += 1
    return res


def add(xs, ys):
    """
    Add two multisets

    >>> list(add([("a", 1), ("b", 2)], [("a", 1), ("c", 3)]))
    [('a', 2), ('b', 2), ('c', 3)]

    """
    res = []
    i, j = 0, 0
    while i < len(xs) and j < len(ys):
        x, n = xs[i]
        y, m = ys[j]
        if x < y:
            res.append((x, n))
            i += 1
        elif x > y:
            res.append((y, m))
            j += 1
        else:
            res.append((x, n + m))
            i += 1
            j += 1
    while i < len(xs):
        assert j == len(ys)
        res.append((xs[i]))
        i += 1
    while j < len(ys):
        assert i == len(xs)
        res.append((ys[j]))
        j += 1
    return res


def sub(xs, ys):
    """Difference two multisets. Return None if the second is not a submultiset of the first

    >>> sub([("a", 1), ("b", 2)], [("a", 1), ("c", 3)]) is None
    True
    >>> sub([("a", 1), ("b", 2)], [("a", 1), ("b", 2)])
    []
    """
    res = []
    i, j = 0, 0
    while i < len(xs) and j < len(ys):
        x, n = xs[i]
        y, m = ys[j]
        if x < y:
            res.append((x, n))
            i += 1
        elif x > y:
            return None
        else:
            if n == m:
                pass
            elif n > m:
                res.append((x, n - m))
            else:
                return None
            i += 1
            j += 1
    if j != len(ys):
        return None
    while i < len(xs):
        res.append(xs[i])
        i += 1
    return res


def replace(xs, lhs, rhs):
    """
    Replace multiset pattern lhs in multiset xs with rhs.

    >>> replace([("a", 1), ("b", 2)], [("a", 1)], [("a", 2), ("c", 3)])
    [('a', 2), ('b', 2), ('c', 3)]
    >>> replace([("a", 1), ("b", 2)], [("a", 1), ("b", 2)], [("a", 2), ("c", 3)])
    [('a', 2), ('c', 3)]
    >>> replace([("a", 1), ("b", 2)], [("a", 1), ("b", 4)], [("a", 2)]) == None
    True
    >>> replace([('p', 25)], [('p', 25)], [('q', 1)])
    [('q', 1)]

    """
    z = sub(xs, lhs)
    if z is None:
        return None
    else:
        return add(z, rhs)


def rewrite(s, R):
    done = False
    while not done:
        done = True
        for i, (lhs, rhs) in enumerate(R):
            s1 = replace(s, lhs, rhs)
            if s1 is not None:
                s = s1
                done = False
    return s


def ms_order(xs, ys):
    for (x, n), (y, m) in zip(xs, ys):
        if x < y:
            return ys, xs
        elif x > y:
            return xs, ys
        elif x == y:
            if n < m:
                return ys, xs
            elif n > m:
                return xs, ys
            elif n == m:
                continue
    assert False, "equal multisets"


def count(xs):
    return sum(n for x, n in xs)


# shrinking with ms to tie break. Is this well founded? substitution stable?
# yes, it is graded lex  https://en.wikipedia.org/wiki/Monomial_order#Graded_lexicographic_order
def shortlex(xs, ys):
    cx, cy = count(xs), count(ys)
    if cx < cy:
        return ys, xs
    elif cx > cy:
        return xs, ys
    else:
        return ms_order(xs, ys)


def deduce(R):
    """deduce all possible critical pairs from R"""
    for i, (lhs, rhs) in enumerate(R):
        for j in range(i):
            lhs1, rhs1 = R[j]
            o = overlap(lhs1, lhs)
            if o is not None:
                x, y = replace(o, lhs1, rhs1), replace(o, lhs, rhs)
                assert x is not None and y is not None
                if x != y:
                    yield x, y


def KB(E):
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
                lhs, rhs = shortlex(lhs, rhs)
                R.append((lhs, rhs))
    return R
