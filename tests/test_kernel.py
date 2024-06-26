import pytest
from knuckledragger import lemma, axiom
from z3 import *

import knuckledragger.theories.Nat
import knuckledragger.theories.Int
import knuckledragger.theories.Real

import knuckledragger.theories.List
import knuckledragger.theories.Seq


def test_true_infer():
    lemma(BoolVal(True))


def test_false_infer():
    with pytest.raises(Exception) as e_info:
        lemma(BoolVal(False))


def test_explosion():
    a = axiom(BoolVal(False), "False axiom")
    with pytest.raises(Exception) as e_info:
        lemma(BoolVal(True), by=[a])


from knuckledragger.utils import calc


def test_calc():
    x, y, z = Ints("x y z")
    l1 = axiom(x == y)
    l2 = axiom(y == z)
    calc(x, l1, y, l2, z)


def test_tptp():
    x = Int("x")
    assert And(x > 4, x <= 7).tptp() == "($greater(x,4) & $lesseq(x,7))"
    assert IntSort().tptp() == "$int"
    assert BoolSort().tptp() == "$o"
    assert (
        ArraySort(ArraySort(BoolSort(), IntSort()), IntSort()).tptp()
        == "(($o > $int) > $int)"
    )
