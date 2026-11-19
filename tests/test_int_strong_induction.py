import pytest

from kdrag import Lemma, define
from kdrag.notation import induct_int_strong
from kdrag.smt import Abs, Bool, ForAll, FreshFunction, If, Int, IntSort, Real


def test_strong_integer_induction_handles_both_signs_and_a_two_step_call():
    n = Int("strong_n")
    f = FreshFunction(IntSort(), IntSort())
    f = define(f.name(), n, If(Abs(n) <= 1, 0, 1 + f(If(n > 0, n - 2, n + 2))))
    pf = Lemma(ForAll([n], f(n) >= 0))
    n = pf.fix()
    pf.induct(n, using=induct_int_strong)
    k = pf.fix()
    ih = pf.intro()
    pf.cases(Abs(k) <= 1, k > 1, k < -1)
    pf.auto(by=[f.defn(k)])
    pf.specialize(ih, k - 2)
    pf.auto(by=[f.defn(k)])
    pf.specialize(ih, k + 2)
    pf.auto(by=[f.defn(k)])
    pf.qed()


@pytest.mark.parametrize("x", [Real("not_integer"), Bool("not_integer")])
def test_strong_integer_induction_rejects_other_sorts(x):
    with pytest.raises(TypeError, match="integer argument"):
        induct_int_strong(x, lambda _: True)
