"""Importing this module will add some syntactic sugar to Z3.

- Expr overload by single dispatch
- Bool supports `&`, `|`, `~`
- Sorts supports `>>` for ArraySort
- Datatypes support accessor notation
"""

import z3


z3.BoolRef.__and__ = lambda self, other: z3.And(self, other)
z3.BoolRef.__or__ = lambda self, other: z3.Or(self, other)
z3.BoolRef.__invert__ = lambda self: z3.Not(self)


def QForAll(vars, hyp, conc):
    """Quantified ForAll

    Shorthand for `ForAll(vars, Implies(hyp, conc))`

    """
    return z3.ForAll(vars, z3.Implies(hyp, conc))


def QExists(vars, hyp, conc):
    """Quantified Exists

    Shorthand for `Exists(vars, And(hyp, conc))`

    """
    return z3.Exists(vars, z3.And(hyp, conc))


z3.SortRef.__rshift__ = lambda self, other: z3.ArraySort(self, other)


class SortDispatch:
    """
    Sort dispatch is modelled after functools.singledispatch
    It allows for dispatching on the sort of the first argument
    """

    def __init__(self, default=None):
        self.methods = {}
        self.default = default

    def register(self, sort, func):
        self.methods[sort] = func

    def __call__(self, *args, **kwargs):
        return self.methods.get(args[0].sort(), self.default)(*args, **kwargs)


add = SortDispatch(z3.ArithRef.__add__)
z3.ExprRef.__add__ = lambda x, y: add(x, y)

sub = SortDispatch(z3.ArithRef.__sub__)
z3.ExprRef.__sub__ = lambda x, y: sub(x, y)

mul = SortDispatch(z3.ArithRef.__mul__)
z3.ExprRef.__mul__ = lambda x, y: mul(x, y)

div = SortDispatch(z3.ArithRef.__div__)
z3.ExprRef.__truediv__ = lambda x, y: div(x, y)

and_ = SortDispatch()
z3.ExprRef.__and__ = lambda x, y: and_(x, y)

or_ = SortDispatch()
z3.ExprRef.__or__ = lambda x, y: or_(x, y)

lt = SortDispatch(z3.ArithRef.__lt__)
z3.ExprRef.__lt__ = lambda x, y: lt(x, y)

le = SortDispatch(z3.ArithRef.__le__)
z3.ExprRef.__le__ = lambda x, y: le(x, y)


"""
mul = SortDispatch(z3.ArithRef.__mul__)
z3.ExprRef.__mul__ = mul

sub = SortDispatch(z3.ArithRef.__sub__)
z3.ExprRef.__sub__ = sub

matmul = SortDispatch()
z3.ExprRef.__matmul__ = matmul

le = SortDispatch()
z3.ExprRef.__le__ = le
"""


def lookup_cons_recog(self, k):
    """
    Enable "dot" syntax for fields of z3 datatypes
    """
    sort = self.sort()
    recog = "is_" == k[:3] if len(k) > 3 else False
    for i in range(sort.num_constructors()):
        cons = sort.constructor(i)
        if recog:
            if cons.name() == k[3:]:
                recog = sort.recognizer(i)
                return recog(self)
        else:
            for j in range(cons.arity()):
                acc = sort.accessor(i, j)
                if acc.name() == k:
                    return acc(self)


z3.DatatypeRef.__getattr__ = lookup_cons_recog
