"""Sine constructed from its power series."""

from kdrag import Theorem, define, kernel, prove
from kdrag.contrib.analysis.deriv import has_deriv_at, has_deriv_at_iff_remainder
from kdrag.contrib.analysis.series import (
    exists_has_sum_of_geometric_decay,
    has_sum_error_of_geometric_decay,
)
from kdrag.smt import Exists, ForAll, Int, IntVal, Lambda, Real, RealVal, ToInt, ToReal
from kdrag.theories.int import fact, fact_ge_1
import kdrag.theories.real as real
from kdrag.theories.real.rseq import cumsum, cumsum_succ, has_sum

x, S = Real("x"), Real("S")
n = Int("n")


sin_terms = define(
    "analysis.sin_terms",
    x,
    Lambda(
        n,
        real.pownat(RealVal(-1), n)
        * real.pownat(x, 2 * n + 1)
        / ToReal(fact(2 * n + 1)),
    ),
)


@Theorem(ForAll(x, sin_terms(x)[0] == x))
def sin_terms_zero(l):
    x = l.fix()
    l.auto(
        by=[
            sin_terms.defn(x),
            real.pownat_zero(RealVal(-1)),
            real.pownat_succ(x, 0),
            real.pownat_zero(x),
            fact.defn(IntVal(1)),
            fact.defn(IntVal(0)),
        ]
    )


@Theorem(
    ForAll(
        [x, n],
        n >= 0,
        sin_terms(x)[n + 1]
        == -(x * x) / (ToReal(2 * n + 2) * ToReal(2 * n + 3)) * sin_terms(x)[n],
    )
)
def sin_terms_succ(l):
    x, n = l.fixes()
    l.intro()
    odd = 2 * n + 1
    l.have(
        fact(odd + 2) == (odd + 2) * (odd + 1) * fact(odd),
        by=[fact.defn(odd + 2), fact.defn(odd + 1)],
    )
    l.have(
        real.pownat(x, odd + 2) == x * x * real.pownat(x, odd),
        by=[real.pownat_succ(x, odd + 1), real.pownat_succ(x, odd)],
    )
    l.auto(by=[sin_terms.defn(x), real.pownat_succ(RealVal(-1), n), fact_ge_1(odd)])


@Theorem(
    ForAll(
        [x, n],
        n >= 0,
        real.abs(sin_terms(x)[n + 1])
        == (x * x)
        / (ToReal(2 * n + 2) * ToReal(2 * n + 3))
        * real.abs(sin_terms(x)[n]),
    )
)
def abs_sin_terms_succ(l):
    x, n = l.fixes()
    l.intro()
    ratio = -(x * x) / (ToReal(2 * n + 2) * ToReal(2 * n + 3))
    l.auto(
        by=[
            sin_terms_succ(x, n),
            real.abs_mul(ratio, sin_terms(x)[n]),
            real.abs.defn(ratio),
        ]
    )


@Theorem(ForAll(x, Exists(S, has_sum(sin_terms(x), S))))
def exists_has_sum_sin_terms(l):
    x = l.fix()
    cutoff = ToInt(x * x) + 1
    half = RealVal("1/2")
    l.have(
        ForAll(
            n,
            n >= cutoff,
            real.abs(sin_terms(x)[n + 1]) <= half * real.abs(sin_terms(x)[n]),
        )
    )
    index = l.fix()
    l.intro()
    l.have(index >= 0, by=[])
    l.have(x * x <= ToReal(index), by=[])
    l.have(
        x * x / (ToReal(2 * index + 2) * ToReal(2 * index + 3)) <= half,
        by=[],
    )
    l.auto(by=[abs_sin_terms_succ(x, index), real.abs_pos(sin_terms(x)[index])])
    l.auto(by=[exists_has_sum_of_geometric_decay(sin_terms(x), half, cutoff)])


(_sine,), _sine_spec = kernel.choose(exists_has_sum_sin_terms)
sin_series = define("analysis.sin_series", x, _sine(x))
has_sum_sin_terms = prove(
    ForAll(x, has_sum(sin_terms(x), sin_series(x))),
    by=[sin_series.defn, _sine_spec],
)


@Theorem(
    ForAll(x, real.abs(x) <= 1, real.abs(sin_series(x) - x) <= real.abs(x) * x * x / 5)
)
def sin_series_error(l):
    x = l.fix()
    l.intro()
    terms = sin_terms(x)
    sixth = RealVal("1/6")
    l.have(x * x <= 1, by=[real.abs.defn(x)])
    l.have(ForAll(n, n >= 1, real.abs(terms[n + 1]) <= sixth * real.abs(terms[n])))
    index = l.fix()
    l.intro()
    l.have(x * x / (ToReal(2 * index + 2) * ToReal(2 * index + 3)) <= sixth, by=[])
    l.auto(by=[abs_sin_terms_succ(x, index), real.abs_pos(terms[index])])
    l.have(
        cumsum(terms)[1] == x,
        by=[cumsum_succ(terms, 0), cumsum.defn(terms), sin_terms_zero(x)],
    )
    l.have(
        real.abs(terms[1]) == real.abs(x) * x * x / 6,
        by=[abs_sin_terms_succ(x, 0), sin_terms_zero(x)],
    )
    l.auto(
        by=[
            has_sum_sin_terms(x),
            has_sum_error_of_geometric_decay(terms, sixth, 1, sin_series(x)),
        ]
    )


@Theorem(sin_series(0) == 0)
def sin_series_zero(l):
    l.auto(by=[sin_series_error(0), real.abs.defn(0), real.abs.defn(sin_series(0))])


@Theorem(has_deriv_at(Lambda(x, sin_series(x)), 1, 0))
def has_deriv_at_sin_series_zero(l):
    l.rw(has_deriv_at_iff_remainder)
    epsilon = l.fix()
    l.intro()
    l.exists(real.min(1, epsilon))
    l.split()
    l.auto(by=[real.min.defn(1, epsilon)])

    x = l.fix()
    l.intro()
    l.beta()
    l.have(real.abs(x) < 1, by=[real.min.defn(1, epsilon)])
    l.have(real.abs(x) < epsilon, by=[real.min.defn(1, epsilon)])
    l.have(x * x / 5 <= epsilon, by=[real.abs.defn(x)])
    l.auto(by=[sin_series_error(x), sin_series_zero, real.abs_pos(x)])


@Theorem(real.has_lim_at(Lambda(x, sin_series(x) / x), 0, 1))
def has_lim_at_sin_series_div_zero(l):
    l.auto(
        by=[
            has_deriv_at_sin_series_zero,
            has_deriv_at.defn(Lambda(x, sin_series(x)), 1, 0),
            sin_series_zero,
        ]
    )
