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
from . import utils
from . import datatype
from . import rewrite
from . import tactics


Proof = kernel.Proof


prove = tactics.prove


axiom = kernel.axiom


define = kernel.define


QForAll = notation.QForAll


QExists = notation.QExists


cond = notation.cond


Inductive = kernel.Inductive


Record = datatype.Record


NewType = datatype.NewType


InductiveRel = datatype.InductiveRel


Enum = datatype.Enum


Calc = tactics.Calc


Lemma = tactics.Lemma

simp = rewrite.simp

search = utils.search

# TODO: Remove this
R = smt.RealSort()
Z = smt.IntSort()
RSeq = Z >> R
RFun = R >> R

__all__ = [
    "prove",
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
    "simp",
    "search",
]
