import pytest
from knuckledragger import lemma, axiom
from z3 import *

import knuckledragger.theories.Nat
import knuckledragger.theories.Int
import knuckledragger.theories.Real


def test_true_infer():
    lemma(BoolVal(True))


def test_false_infer():
    with pytest.raises(Exception) as e_info:
        lemma(BoolVal(False))


def test_explosion():
    a = axiom(RealVal(1) == RealVal(0), "False axiom")
    lemma(BoolVal(False), by=[a])
