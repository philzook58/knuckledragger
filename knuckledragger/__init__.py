from . import kernel
from . import notation
from . import tactics
import knuckledragger.smt as smt

lemma = tactics.lemma
axiom = kernel.axiom
define = kernel.define

QForAll = notation.QForAll
QExists = notation.QExists
Cond = notation.Cond
Record = notation.Record

Calc = tactics.Calc

R = smt.RealSort()
Z = smt.IntSort()
RSeq = Z >> R
RFun = R >> R
