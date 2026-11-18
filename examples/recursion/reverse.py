"""Sequence reverse from checked integer recursion with a sufficient gas bound.

Run: PYTHONPATH=src python examples/recursion/reverse.py
Only rev_aux is admitted by the experimental integer-recursion rule. Reverse's
head/tail equation is proved from that equation and a gas-independence lemma.
"""

from kdrag import Tail, Theorem
from kdrag.kernel import define_simple
from kdrag.smt import (
    Const,
    DeclareSort,
    Empty,
    ForAll,
    Function,
    If,
    IntSort,
    Ints,
    Length,
    Or,
    SeqSort,
)
from kdrag.tactics import ProofState
from kdrag.termination import define_rec

Element = DeclareSort("GasReverse.Element")
S = SeqSort(Element)
xs = Const("xs", S)
gas, more = Ints("gas more")


rev_aux = Function("GasReverse.rev_aux", IntSort(), S, S)
define_rec(
    rev_aux,
    [gas, xs],
    If(Or(gas <= 0, Length(xs) == 0), Empty(S), rev_aux(gas - 1, Tail(xs)) + [xs[0]]),
)
rev = define_simple("GasReverse.rev", [xs], rev_aux(Length(xs), xs))


@Theorem(
    ForAll(
        [xs],
        ForAll(
            [gas, more],
            gas >= Length(xs),
            more >= Length(xs),
            rev_aux(gas, xs) == rev_aux(more, xs),
        ),
    )
)
def enough_gas(pf: ProofState):
    """Once both budgets cover the length, their results agree."""
    xs = pf.fix()
    pf.induct(xs)
    pf.auto(by=[rev_aux.defn])
    x, xs = pf.fixes()
    pf.intros()
    gas, more = pf.fixes()
    pf.intros()
    pf.intros()
    whole = [x] + xs
    pf.auto(by=[rev_aux.defn(gas, whole), rev_aux.defn(more, whole)])


@Theorem(
    ForAll([xs], rev(xs) == If(Length(xs) == 0, Empty(S), rev(Tail(xs)) + [xs[0]]))
)
def rev_eq(pf: ProofState):
    """The usual reverse equation, derived after fixing gas to the length."""
    xs = pf.fix()
    pf.cases(Length(xs) == 0)
    pf.auto(by=[rev.defn(xs), rev_aux.defn(Length(xs), xs)])
    pf.auto(
        by=[
            rev.defn(xs),
            rev_aux.defn(Length(xs), xs),
            rev.defn(Tail(xs)),
            enough_gas(Tail(xs), Length(xs) - 1, Length(Tail(xs))),
        ]
    )


if __name__ == "__main__":
    print(rev_eq)
