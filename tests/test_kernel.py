import pytest
from knuckledragger.kernel import *
import z3


def test_true_infer():
    infer([], True)


def test_false_infer():
    with pytest.raises(Exception) as e_info:
        infer([], False)


def test_explosion():
    a = trust(False)
    infer([a], False)
