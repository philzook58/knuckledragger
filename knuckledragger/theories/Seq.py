from knuckledragger.theories.Nat import Nat
from knuckledragger.theories.Real import R
from z3 import ArraySort

"""A Sequence type of Nat -> R"""
Seq = ArraySort(Nat, R)
