from . import smt
from . import kernel
from . import notation
from . import tactics
from . import utils as utils


lemma = tactics.lemma
axiom = kernel.axiom
define = kernel.define
Proof = kernel.Proof

QForAll = notation.QForAll
QExists = notation.QExists
cond = notation.cond
Record = notation.Record
NewType = notation.NewType

Calc = tactics.Calc

R = smt.RealSort()
Z = smt.IntSort()
RSeq = Z >> R
RFun = R >> R
