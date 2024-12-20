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
Inductive = notation.Inductive

Calc = tactics.Calc
Lemma = tactics.Lemma

R = smt.RealSort()
Z = smt.IntSort()
RSeq = Z >> R
RFun = R >> R

__all__ = [
    "lemma",
    "axiom",
    "define",
    "Proof",
    "QForAll",
    "QExists",
    "cond",
    "Record",
    "NewType",
    "Inductive",
    "Calc",
    "Lemma",
    "R",
    "Z",
    "RSeq",
    "RFun",
]
