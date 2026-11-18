import pytest

import kdrag as kd
import kdrag.smt as smt


@pytest.mark.parametrize(
    "sort",
    [
        smt.SeqSort(smt.IntSort()),
        smt.SeqSort(smt.RealSort()),
        smt.SeqSort(smt.DeclareSort("SeqInductElement")),
        smt.SeqSort(smt.SeqSort(smt.IntSort())),
        smt.StringSort(),
    ],
)
def test_default_sequence_induction_has_empty_cons_cases(sort):
    xs = smt.Const("xs", sort)
    goal = smt.ForAll([xs], smt.Length(xs) >= 0)
    pf = kd.Lemma(goal)
    xs = pf.fix()
    pf.induct(xs)
    pf.auto()
    head, tail = pf.fixes()
    assert head.sort() == sort.basis()
    assert tail.sort() == sort
    pf.intros()
    pf.auto()
    assert pf.qed().thm.eq(goal)


def test_explicit_concatenation_induction_is_preserved():
    xs = smt.Const("xs", smt.SeqSort(smt.IntSort()))
    schema = kd.notation.induct_seq(xs, lambda s: smt.Length(s) >= 0)
    assert len(schema.thm.arg(0).children()) == 3
    kd.prove(smt.Length(xs) >= 0, by=[schema])
