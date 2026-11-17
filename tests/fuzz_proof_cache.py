"""
Randomized tests of the proof cache key with hypothesis. Run by hand when changing `kdrag.proof_cache`:
`python -m pytest tests/fuzz_proof_cache.py` (about a minute). The file name keeps it out of normal test runs.

Unrelated random formulas almost never share a key, so a pair of formulas here shares one shape and fills it
twice with confusable pieces: same-named constants of different sorts, fresh-looking names, sorts that print
alike (the int symbol 3 and the string "k!3"), datatypes sharing constructor and accessor names, overloaded
`f` and `p`, and binders named like constants (variable capture).
Equal keys must mean the formulas are equal up to renaming fresh names, judged by z3's own equality.
"""

import functools
import re

import z3
from hypothesis import HealthCheck, event, given, settings
from hypothesis import strategies as st
from z3.z3 import _to_expr_ref

from kdrag import proof_cache

ctx = z3.main_ctx()
INT3 = 3  # stands for the int symbol 3, which prints as k!3


def int_symbol_sort(n: int) -> z3.SortRef:
    return z3.SortRef(
        z3.Z3_mk_uninterpreted_sort(ctx.ref(), z3.Z3_mk_int_symbol(ctx.ref(), n)), ctx
    )


def datatype(name: str, field: z3.SortRef) -> z3.DatatypeSortRef:
    d = z3.Datatype(name)
    d.declare("mk", ("fld", field))
    d.declare("nil")
    return d.create()


K3_STR = z3.DeclareSort("k!3")
K3_INT = int_symbol_sort(INT3)
DATATYPES = [
    datatype("FuzzA", z3.IntSort()),
    datatype("FuzzB", z3.IntSort()),
    datatype("FuzzC", z3.RealSort()),
]
SORTS = [
    z3.IntSort(),
    z3.RealSort(),
    z3.BoolSort(),
    z3.BitVecSort(4),
    z3.BitVecSort(8),
    z3.StringSort(),
    z3.DeclareSort("FuzzU"),
    K3_STR,
    K3_INT,
    *DATATYPES,
    z3.ArraySort(K3_STR, z3.BoolSort()),
    z3.ArraySort(K3_INT, z3.BoolSort()),
]
NAMES = ["x", "y", "x!1", "x!2", "k!3", INT3]
FRESH_PREFIXES = ["x", "k"]

# A shape is an untyped formula tree. Sorts come from sort variables 0-2, names from name slots 0-3.
SORT_VAR = st.integers(0, 2)
NAME_SLOT = st.integers(0, 3)


@functools.cache
def formulas_of_depth(d: int) -> st.SearchStrategy:
    term = terms_of_depth(max(d - 1, 0))
    atoms = [
        st.tuples(st.just("eq"), SORT_VAR, term, term),
        st.tuples(st.just("pred"), SORT_VAR, term),
        st.tuples(st.just("distinct"), SORT_VAR, term, term, term),
    ]
    if d == 0:
        return st.one_of(atoms)
    sub = formulas_of_depth(d - 1)
    return st.one_of(
        *atoms,
        st.tuples(st.just("not"), sub),
        st.tuples(st.sampled_from(["and", "or", "implies"]), sub, sub),
        st.tuples(
            st.just("quant"),
            st.sampled_from(["forall", "exists"]),
            SORT_VAR,
            NAME_SLOT,
            sub,
        ),
    )


@functools.cache
def terms_of_depth(d: int) -> st.SearchStrategy:
    leaves = [
        st.tuples(st.just("const"), NAME_SLOT),
        st.tuples(st.just("fresh"), st.integers(0, 1), st.integers(0, 2)),
        st.tuples(st.just("num"), st.integers(-2, 2)),
    ]
    if d == 0:
        return st.one_of(leaves)
    sub, cond = terms_of_depth(d - 1), formulas_of_depth(d - 1)
    return st.one_of(
        *leaves,
        st.tuples(st.just("app"), SORT_VAR, sub),
        st.tuples(st.just("ite"), cond, sub, sub),
        st.tuples(st.just("select"), SORT_VAR, sub),
        st.tuples(st.just("lambda"), SORT_VAR, NAME_SLOT, sub, sub),
        st.tuples(st.just("field"), st.integers(0, 2), sub),
        st.tuples(st.just("mk"), sub),
    )


formulas = formulas_of_depth(4)
# How to fill a shape: a sort for each sort variable and a name for each name slot.
fillings = st.tuples(
    st.lists(st.sampled_from(SORTS), min_size=3, max_size=3),
    st.lists(st.sampled_from(NAMES), min_size=4, max_size=4),
)


class Builder:
    """Build the formula of a shape and a filling. Fresh constants are new for every Builder."""

    def __init__(self, filling):
        self.sorts, self.names = filling
        self.fresh = {}

    def const(self, slot: int, s: z3.SortRef) -> z3.ExprRef:
        name = self.names[slot]
        if name == INT3:
            return _to_expr_ref(
                z3.Z3_mk_const(ctx.ref(), z3.Z3_mk_int_symbol(ctx.ref(), INT3), s.ast),
                ctx,
            )
        return z3.Const(name, s)

    def formula(self, n) -> z3.BoolRef:
        tag = n[0]
        if tag == "eq":
            s = self.sorts[n[1]]
            return self.term(n[2], s) == self.term(n[3], s)
        if tag == "pred":
            s = self.sorts[n[1]]
            return z3.Function("p", s, z3.BoolSort())(self.term(n[2], s))
        if tag == "not":
            return z3.Not(self.formula(n[1]))
        if tag in ("and", "or", "implies"):
            op = {"and": z3.And, "or": z3.Or, "implies": z3.Implies}[tag]
            return op(self.formula(n[1]), self.formula(n[2]))
        if tag == "quant":
            # Binding by name captures any constant in the body with the binder's name and sort.
            x = self.const(n[3], self.sorts[n[2]])
            return (z3.ForAll if n[1] == "forall" else z3.Exists)(
                [x], self.formula(n[4])
            )
        if tag == "distinct":
            s = self.sorts[n[1]]
            return z3.Distinct(*(self.term(t, s) for t in n[2:]))
        raise ValueError(n)

    def term(self, n, s: z3.SortRef) -> z3.ExprRef:
        tag = n[0]
        if tag == "fresh":
            k = (n[1], n[2], s.get_id())
            if k not in self.fresh:
                self.fresh[k] = (s, z3.FreshConst(s, prefix=FRESH_PREFIXES[n[1]]))
            return self.fresh[k][1]
        if tag == "num" and s.kind() in (z3.Z3_INT_SORT, z3.Z3_REAL_SORT):
            return z3.IntVal(n[1]) if s.kind() == z3.Z3_INT_SORT else z3.RealVal(n[1])
        if tag == "num" and s.kind() == z3.Z3_BV_SORT:
            return z3.BitVecVal(n[1], s)
        if tag == "app":
            a = self.sorts[n[1]]
            return z3.Function("f", a, s)(self.term(n[2], a))
        if tag == "ite":
            return z3.If(self.formula(n[1]), self.term(n[2], s), self.term(n[3], s))
        if tag == "select":
            a = self.sorts[n[1]]
            return z3.Const("arr", z3.ArraySort(a, s))[self.term(n[2], a)]
        if tag == "lambda":
            a = self.sorts[n[1]]
            x = self.const(n[2], a)
            return z3.Lambda([x], self.term(n[3], s))[self.term(n[4], a)]
        if tag == "field":
            d = DATATYPES[n[1]]
            if d.accessor(0, 0).range().eq(s):
                return d.accessor(0, 0)(self.term(n[2], d))
        if tag == "mk" and isinstance(s, z3.DatatypeSortRef):
            return s.constructor(0)(self.term(n[1], s.accessor(0, 0).range()))
        return self.const(
            0, s
        )  # "const", and the fallback when a tag does not fit the sort


FRESH = re.compile(r"(.*)!([0-9]+)")


def equal_up_to_fresh_names(f: z3.ExprRef, g: z3.ExprRef) -> bool:
    """
    The oracle: whether f and g are equal, by z3's identity of declarations and sorts, up to a bijective renaming
    of fresh-looking declarations (names `p!N`) that keeps the prefix and the signature.
    Bound variables are de Bruijn indices in z3, so their names never matter.
    """
    forward, backward = {}, {}

    def fresh_prefix(d) -> str | None:
        # z3py names the int symbol 3 "k!3", so check the symbol kind directly.
        sym = z3.Z3_get_decl_name(ctx.ref(), d.ast)
        if d.kind() != z3.Z3_OP_UNINTERPRETED:
            return None
        if z3.Z3_get_symbol_kind(ctx.ref(), sym) != z3.Z3_STRING_SYMBOL:
            return None
        m = FRESH.fullmatch(d.name())
        return m[1] if m else None

    def same_decl(d, e):
        pd, pe = fresh_prefix(d), fresh_prefix(e)
        if pd is not None and pe is not None:
            same_sig = d.arity() == e.arity() and d.range().eq(e.range())
            same_sig = same_sig and all(
                d.domain(i).eq(e.domain(i)) for i in range(d.arity())
            )
            if not same_sig or pd != pe:
                return False
            i, j = d.get_id(), e.get_id()
            if forward.setdefault(i, j) != j or backward.setdefault(j, i) != i:
                return False
            return True
        return d.eq(e)

    def same(a, b):
        if z3.is_quantifier(a) or z3.is_quantifier(b):
            if not (z3.is_quantifier(a) and z3.is_quantifier(b)):
                return False
            kinds = (a.is_forall(), a.is_exists(), a.is_lambda()) == (
                b.is_forall(),
                b.is_exists(),
                b.is_lambda(),
            )
            n = a.num_vars()
            sorts = n == b.num_vars() and all(
                a.var_sort(i).eq(b.var_sort(i)) for i in range(n)
            )
            return kinds and sorts and same(a.body(), b.body())
        if z3.is_var(a) or z3.is_var(b):
            return (
                z3.is_var(a)
                and z3.is_var(b)
                and z3.get_var_index(a) == z3.get_var_index(b)
                and a.sort().eq(b.sort())
            )
        if a.num_args() != b.num_args() or not same_decl(a.decl(), b.decl()):
            return False
        return all(same(a.arg(i), b.arg(i)) for i in range(a.num_args()))

    return same(f, g)


# Run by hand when changing `kdrag.proof_cache`: `python -m pytest tests/fuzz_proof_cache.py`. Not collected in CI.
FUZZ = settings(
    max_examples=20_000, deadline=None, suppress_health_check=list(HealthCheck)
)


@FUZZ
@given(formulas, fillings, fillings)
def test_equal_keys_mean_equal_formulas(shape, filling1, filling2):
    f, g = Builder(filling1).formula(shape), Builder(filling2).formula(shape)
    kf, kg = proof_cache.key(f), proof_cache.key(g)
    equal = equal_up_to_fresh_names(f, g)
    if kf is None:
        event("refused")
    elif not equal:
        event("different formulas")
    else:
        # Equal formulas usually share a key, but not always: the key follows z3's sharing, and a binder
        # renamed in one of two equal subterms makes z3 store them twice. That costs a cache miss, not soundness.
        event(
            "equal formulas, same key" if kf == kg else "equal formulas, different keys"
        )
    if kf is not None and kf == kg:
        assert equal, ("different formulas share a key", f.sexpr(), g.sexpr())


@FUZZ
@given(formulas, fillings)
def test_new_fresh_constants_keep_the_key(shape, filling):
    f, g = Builder(filling).formula(shape), Builder(filling).formula(shape)
    assert equal_up_to_fresh_names(f, g)
    assert proof_cache.key(f) == proof_cache.key(g)
