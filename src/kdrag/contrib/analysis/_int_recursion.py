"""Recursion on nonnegative integer indices, proved by extending finite prefixes."""

import kdrag as kd
from kdrag import Proof, Theorem, define
from kdrag.smt import (
    And,
    ArraySort,
    Const,
    Consts,
    Exists,
    ForAll,
    If,
    IntSort,
    Ints,
    K,
    Lambda,
    SortRef,
    Store,
)
import kdrag.theories.int as int_


def int_recursion(sort: SortRef) -> Proof:
    """An initial value and indexed step function admit an integer-indexed orbit."""
    step = Const("step", ArraySort(IntSort(), sort, sort))
    x = Const("x", sort)
    a, b = Consts("a b", ArraySort(IntSort(), sort))
    i, n, N, M = Ints("i n N M")
    prefix = define(
        "analysis.recursion_prefix",
        [step, x, N, a],
        And(a[0] == x, ForAll(i, i >= 0, i < N, a[i + 1] == step[i, a[i]])),
    )

    @Theorem(ForAll([step, x, N], Exists(a, prefix(step, x, N, a))))
    def exists_prefix(l):
        step, x, N = l.fixes()
        base = K(IntSort(), x)
        l.cases(N < 0, N >= 0)
        l.exists(base)
        l.auto(by=[prefix.defn(step, x, N, base)])
        l.induct(N, using=int_.induct_nat)
        l.exists(base)
        l.auto(by=[prefix.defn(step, x, 0, base)])
        j = l.fix()
        _, ih = l.intros()
        partial, _ = l.obtain(ih)
        extended = Store(partial, j + 1, step[j, partial[j]])
        l.exists(extended)
        l.unfold(prefix)
        l.split()
        l.auto(by=[prefix.defn(step, x, j, partial)])
        i = l.fix()
        l.intros()
        l.cases(i == j, i < j)
        l.auto()
        l.have(
            ForAll(n, n >= 0, n < j, partial[n + 1] == step[n, partial[n]]),
            by=[prefix.defn(step, x, j, partial)],
        )
        l.auto()

    @Theorem(
        ForAll(
            [step, x, N, M, a, b, n],
            prefix(step, x, N, a),
            prefix(step, x, M, b),
            n >= 0,
            n <= N,
            n <= M,
            a[n] == b[n],
        )
    )
    def prefixes_agree(l):
        step, x, N, M, a, b, n = l.fixes()
        l.unfold(prefix)
        first = l.intro()
        second = l.intro()
        l.intro()
        _, first_step = l.andE(first)
        _, second_step = l.andE(second)
        l.induct(n, using=int_.induct_nat)
        l.auto()
        j = l.fix()
        l.intros()
        l.specialize(first_step, j)
        l.specialize(second_step, j)
        l.auto()

    (selected,), selected_valid = kd.kernel.choose(exists_prefix)

    @Theorem(
        ForAll(
            [step, x],
            Exists(
                a,
                And(
                    ForAll(n, n <= 0, a[n] == x),
                    ForAll(n, n >= 0, a[n + 1] == step[n, a[n]]),
                ),
            ),
        )
    )
    def exists_recurrence(l):
        step, x = l.fixes()
        l.exists(Lambda(n, If(n < 0, x, selected(step, x, n)[n])))
        l.split()
        j = l.fix()
        l.intro()
        l.auto(
            by=[
                selected_valid(step, x, 0),
                prefix.defn(step, x, 0, selected(step, x, 0)),
            ]
        )
        j = l.fix()
        l.intro()
        short, long = selected(step, x, j), selected(step, x, j + 1)
        # The longer prefix agrees at j and supplies the step to j + 1.
        l.have(
            short[j] == long[j],
            by=[
                selected_valid(step, x, j),
                selected_valid(step, x, j + 1),
                prefixes_agree(step, x, j, j + 1, short, long, j),
            ],
        )
        l.have(
            ForAll(i, i >= 0, i < j + 1, long[i + 1] == step[i, long[i]]),
            by=[selected_valid(step, x, j + 1), prefix.defn(step, x, j + 1, long)],
        )
        l.auto()

    return exists_recurrence
