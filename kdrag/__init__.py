from . import smt
from . import kernel
from . import notation
from . import tactics
from . import utils as utils

Proof = kernel.Proof
"""The type of Proof objects"""

lemma = tactics.lemma
"""Declare a lemma with auto generated proof. `by` keyword argument can be used to provide a list of previously proved lemmas"""

axiom = kernel.axiom
"""Declare an axiom"""

define = kernel.define
"""Declare a definition"""

QForAll = notation.QForAll
"""Quantified forall. Auto adds well formedness `wf(x)`"""

QExists = notation.QExists
"""Quantified exists. Auto adds well formedness `wf(x)`"""

cond = notation.cond
"""Helper for conditional expressions (chained If)"""

Record = notation.Record
"""Declare a record type"""

NewType = notation.NewType
"""Declare a newtype"""

Inductive = notation.Inductive
"""Declare datatypes with auto generated induction principles"""

Calc = tactics.Calc
"""Tactic class for calculation style proofs"""

Lemma = tactics.Lemma
"""Tactic class for interactive proofs"""

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
