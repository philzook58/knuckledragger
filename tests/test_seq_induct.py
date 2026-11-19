import pytest

from kdrag import Lemma, prove
from kdrag.notation import induct_seq
from kdrag.smt import (
    Const,
    DeclareSort,
    ForAll,
    IntSort,
    Length,
    RealSort,
    SeqSort,
    StringSort,
)


@pytest.mark.parametrize(
    "sort",
    [
        SeqSort(IntSort()),
        SeqSort(RealSort()),
        SeqSort(DeclareSort("SeqInductElement")),
        SeqSort(SeqSort(IntSort())),
        StringSort(),
    ],
)
def test_default_sequence_induction_has_empty_cons_cases(sort):
    xs = Const("xs", sort)
    goal = ForAll([xs], Length(xs) >= 0)
    pf = Lemma(goal)
    xs = pf.fix()
    pf.induct(xs)
    pf.auto()
    head, tail = pf.fixes()
    assert head.sort() == sort.basis()
    assert tail.sort() == sort
    pf.intro()
    pf.auto()
    assert pf.qed().thm.eq(goal)


def test_explicit_concatenation_induction_is_preserved():
    xs = Const("xs", SeqSort(IntSort()))
    schema = induct_seq(xs, lambda s: Length(s) >= 0)
    assert len(schema.thm.arg(0).children()) == 3
    prove(Length(xs) >= 0, by=[schema])
