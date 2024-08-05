from . import kernel
from . import notation
from . import tactics
import z3

lemma = tactics.lemma
axiom = kernel.axiom
define = kernel.define

QForAll = notation.QForAll
QExists = notation.QExists

Calc = tactics.Calc

R = z3.RealSort()
Z = z3.IntSort()
RSeq = Z >> R
RFun = R >> R
