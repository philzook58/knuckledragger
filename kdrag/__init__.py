"""
Knuckledragger is an attempt at creating a down to earth,
highly automated interactive proof assistant in python.
It is not attempting to be the most interesting, expressive,
or flexible logic in the world.

The goal is to support applications like software/hardware verification,
calculus, equational reasoning, and numerical bounds.
"""

from . import smt
from . import kernel
from . import notation
from . import datatype
from . import tactics
from . import utils as utils

Proof = kernel.Proof


lemma = tactics.lemma


axiom = kernel.axiom


define = kernel.define


QForAll = notation.QForAll


QExists = notation.QExists


cond = notation.cond


Record = datatype.Record


NewType = datatype.NewType


Inductive = datatype.Inductive


Enum = datatype.Enum


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
