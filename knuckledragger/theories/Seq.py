import knuckledragger.theories.Nat as Nat
import knuckledragger.theories.Real as Real
from z3 import ArraySort

Seq = ArraySort(Nat.Nat, Real.R)
