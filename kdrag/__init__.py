from . import smt
from . import kernel
from . import notation
from . import tactics
from . import utils as utils

Proof = kernel.Proof


lemma = tactics.lemma


axiom = kernel.axiom


define = kernel.define


QForAll = notation.QForAll


QExists = notation.QExists


cond = notation.cond


Record = notation.Record


NewType = notation.NewType


Inductive = notation.Inductive


Enum = notation.Enum


Calc = tactics.Calc


Lemma = tactics.Lemma


# TODO: Remove this
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
