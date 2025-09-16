"""
Helper functions for the hypothesis property based testing library.

This can be useful for:
- Giving counterexamples to poorly stated theorems before you spend much effort on them
- Sanity checking axioms
- Connecting formal models to other code
- Testing Knuckledragger facilities
- Testing Z3 intended meaning
"""

import kdrag as kd
import kdrag.smt as smt
import hypothesis
import hypothesis.strategies as st
import operator as op
from typing import Optional

smt_sorts = st.recursive(
    st.sampled_from([smt.BoolSort(), smt.IntSort(), smt.RealSort(), smt.StringSort()]),
    lambda children: st.one_of(
        st.tuples(children, children).map(lambda x: smt.ArraySort(x[0], x[1])),
        children.map(lambda x: smt.SeqSort(x)),
    ),
)

names = st.sampled_from("x y z".split())
# I think we'll get more interesting bugs with more name clashes rather than exploring weird names


def binop(children, op) -> st.SearchStrategy:
    return st.tuples(children, children).map(lambda t: op(t[0], t[1]))


def binops(children) -> st.SearchStrategy:
    return st.one_of(
        binop(children, op.add),
        binop(children, op.sub),
        binop(children, op.mul),
        binop(children, op.truediv),
    )


smt_int_val: st.SearchStrategy[smt.ArithRef] = st.integers().map(smt.IntVal)
smt_int_expr = st.recursive(
    st.one_of(smt_int_val, names.map(smt.Int)),
    lambda children: st.one_of(
        binop(children, op.add),
        binop(children, op.sub),
        binop(children, op.mul),
        binop(children, op.truediv),
        st.deferred(
            lambda: st.tuples(smt_bool_expr, children, children).map(
                lambda x: smt.If(x[0], x[1], x[2])
            )
        ),
    ),
)


smt_bool_val: st.SearchStrategy[smt.BoolRef] = st.sampled_from(
    [smt.BoolVal(True), smt.BoolVal(False)]
)

smt_real_val = st.fractions().map(smt.RealVal)
smt_real_expr = st.recursive(
    st.one_of(
        smt_real_val,
        names.map(smt.Real),
    ),
    lambda children: st.one_of(
        binop(children, op.add),
        binop(children, op.sub),
        binop(children, op.mul),
        binop(children, op.truediv),
        st.deferred(
            lambda: st.tuples(smt_bool_expr, children, children).map(
                lambda x: smt.If(x[0], x[1], x[2])
            )
        ),
    ),
)


def compares(strat) -> st.SearchStrategy:
    return st.one_of(
        binop(strat, op.eq),
        binop(strat, op.ne),
        binop(strat, op.lt),
        binop(strat, op.le),
        binop(strat, op.gt),
        binop(strat, op.ge),
    )


smt_bool_expr = st.recursive(
    st.one_of(
        smt_bool_val,
        names.map(smt.Bool),
        compares(smt_int_expr),
        compares(smt_real_expr),
    ),
    lambda children: st.one_of(
        binop(children, smt.And),
        binop(children, smt.Or),
        binop(children, smt.Xor),
        st.tuples(children, children).map(lambda x: x[0] == x[1]),
        st.tuples(children, children).map(lambda x: smt.Implies(x[0], x[1])),
    ),
)


smt_string_val = st.text().map(smt.StringVal)


def sort_occurs(s, s2, visited=None):
    """
    Check if a sort occurs in the datatype.

    >>> import kdrag.theories.list as list
    >>> sort_occurs(smt.IntSort(), list.List(smt.IntSort()).T)
    True
    >>> sort_occurs(smt.IntSort(), list.List(smt.BoolSort()).T)
    False
    >>> sort_occurs(smt.IntSort(), smt.IntSort())
    True
    """
    if visited is None:
        visited = set()
    if s2 in visited:
        return False
    elif s == s2:
        return True
    elif isinstance(s2, smt.ArraySortRef):
        visited.add(s2)
        return sort_occurs(s, s2.domain(), visited=visited) or sort_occurs(
            s, s2.range(), visited=visited
        )
    elif isinstance(s2, smt.SeqSortRef):
        visited.add(s2)
        return sort_occurs(s, s2.basis(), visited=visited)
    elif isinstance(s2, smt.DatatypeSortRef):
        visited.add(s2)
        for i in range(s2.num_constructors()):
            cons = s2.constructor(i)
            for j in range(cons.arity()):
                field_sort = cons.domain(j)
                if sort_occurs(s, field_sort, visited=visited):
                    return True
        return False
    else:
        return False


def smt_datatype_val(s: smt.DatatypeSortRef) -> st.SearchStrategy[smt.DatatypeRef]:
    # TODO: with a lot of muscle grease, we could probably do better than a big deferred
    bases = []
    for i in range(s.num_constructors()):
        cons = s.constructor(i)
        if cons.arity() == 0:
            bases.append(st.just(cons()))  # optimization
        elif all(not sort_occurs(s, cons.domain(j)) for j in range(cons.arity())):
            args = []
            for j in range(cons.arity()):
                field_sort = cons.domain(j)
                args.append(val_of_sort(field_sort))
            bases.append(st.tuples(*args).map(lambda args: cons(*args)))
    base = st.one_of(bases)

    def rec(children):
        cases = []
        for i in range(s.num_constructors()):
            cons = s.constructor(i)

            def conswrap(*args):
                return cons(*args)

            conswrap.__name__ = cons.name()  # hack to get slightly better output
            if any(sort_occurs(s, cons.domain(j)) for j in range(cons.arity())):
                args = []
                for j in range(cons.arity()):
                    field_sort = cons.domain(j)
                    args.append(val_of_sort(field_sort, knot_tie=(s, children)))
                cases.append(st.tuples(*args).map(conswrap))

        return st.one_of(*cases)

    return st.recursive(base, rec)


def smt_seq_val(s: smt.SortRef) -> st.SearchStrategy[smt.SeqRef]:
    vsort = val_of_sort(s)
    return st.one_of(
        st.just(smt.Empty(smt.SeqSort(s))),
        vsort.map(lambda v: smt.Unit(v)),
        st.lists(vsort, min_size=2).map(
            lambda l: smt.Concat(*[smt.Unit(x) for x in l])
        ),
    )


def z3_array_val(
    dom: st.SearchStrategy[smt.ExprRef], ran: st.SearchStrategy[smt.ExprRef]
) -> st.SearchStrategy[smt.ArrayRef]:
    def of_list(l: list[tuple[smt.ExprRef, smt.ExprRef]]) -> smt.ArrayRef:
        k, v = l.pop()
        acc = smt.K(k.sort(), v)
        for k, v in l:
            acc = smt.Store(acc, k, v)
        return acc

    return st.lists(st.tuples(dom, ran), min_size=1).map(of_list)


def val_of_sort(
    s: smt.SortRef,
    knot_tie: Optional[tuple[smt.SortRef, st.SearchStrategy[smt.ExprRef]]] = None,
    slow_generic=False,
) -> st.SearchStrategy[smt.ExprRef]:
    """
    Make a search strategy of values of a given SMT sort.
    """
    if knot_tie is not None and knot_tie[0] == s:
        return knot_tie[1]
    if s == smt.BoolSort():
        return smt_bool_val
    elif s == smt.IntSort():
        return smt_int_val
    elif s == smt.RealSort():
        return smt_real_val
    elif s == smt.StringSort():
        return smt_string_val
    elif isinstance(s, smt.ArraySortRef):
        return z3_array_val(val_of_sort(s.domain()), val_of_sort(s.range()))
    elif isinstance(s, smt.SeqSortRef):
        return smt_seq_val(s.basis())
    elif isinstance(s, smt.DatatypeSortRef):
        return smt_datatype_val(s)
    else:
        # return smt_generic_val(s) # This is really slow. We're better off just throwing an error
        if slow_generic:
            return smt_generic_val(s)
        else:
            raise NotImplementedError(f"Don't know how to generate values for {s}")


# def expr_of_sort(s: smt.SortRef):


@st.composite
def smt_generic_val(draw: st.DrawFn, sort: smt.SortRef, maxiter=4) -> smt.ExprRef:
    """
    A hypothesis search strateegy that uses smt model generation to generate a value of a given SMT sort. It is slower
    and will have worse shrinkage. To be used as a fallback.
    """
    x, y = smt.Consts("x y", sort)
    s = smt.Solver()
    # s.set("random_seed", draw(st.integers())) # Did not seem to work.
    # According to Z3 docs, Solver is deterministic.
    s.add(x == y)
    res = s.check()
    assert res == smt.sat
    v = s.model()[x]
    for j in range(draw(st.integers(min_value=0, max_value=maxiter))):
        if res == smt.sat:
            v = s.model()[x]
            s.add(v != x)
            res = s.check()
        elif res == smt.unsat:
            break
    return v


def quickcheck(thm: smt.QuantifierRef, deadline=100, **hyp_settings):
    """
    Run a hypothesis test to check that an instantiated forall is equivalent to the original forall.
    """
    assert isinstance(thm, smt.QuantifierRef) and thm.is_forall()
    sorts = [val_of_sort(thm.var_sort(i)) for i in range(thm.num_vars())]
    body = thm.body()
    N = len(sorts)

    # Todo: could specialize to arity of the quantifier. Probably not worth it.
    @hypothesis.settings(deadline=deadline, **hyp_settings)
    @hypothesis.given(**{str(i): sort for i, sort in enumerate(sorts)})
    def quickcheck(**kwargs):
        t0 = smt.substitute_vars(body, *[kwargs[str(i)] for i in range(N - 1, -1, -1)])
        hypothesis.note(("Starting point: ", t0))
        t1 = kd.rewrite.simp(t0, max_iter=1000000000)
        hypothesis.note(("Simplifies to: ", t1))
        if not smt.is_true(t1):
            s = smt.Solver()
            s.set("timeout", 100)
            s.add(smt.Not(t1))
            res = s.check()
            if res == smt.sat:
                model = s.model()
                hypothesis.note(("Counterexample: ", model))
                raise AssertionError("Found a counterexample", model)
            elif res == smt.unsat:
                pass
            else:
                raise AssertionError("Could not find a counterexample")

    quickcheck()
