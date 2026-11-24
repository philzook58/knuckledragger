import pytest

import kdrag as kd
from kdrag import smt


@pytest.mark.parametrize("with_context", [False, True])
def test_split_quantified_equivalence(with_context):
    predicate = smt.Const("split_predicate", smt.SetSort(smt.RealSort()))
    x = smt.Real("x")
    thm = smt.Eq(smt.ForAll(x, predicate[x]), smt.ForAll(x, predicate[-x]))
    if with_context:
        thm = smt.Implies(smt.Bool("split_context"), thm)
    l = kd.Lemma(thm)
    if with_context:
        l.intro()
    l.split()
    h = l.intro()
    x = l.fix()
    l.specialize(h, -x)
    l.auto()
    h = l.intro()
    x = l.fix()
    l.specialize(h, -x)
    l.auto()
    assert l.qed().thm.eq(thm)
