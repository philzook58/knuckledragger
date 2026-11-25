"""Rebuild the original burali_forti step (before f4c9894) and export the failing query."""

import shutil
import kdrag as kd
import kdrag.theories.zf.zf as zf
from kdrag.smt import Consts, Exists, ForAll, Lambda, Not
from kdrag.theories.zf.zf import ZFSet, bigunion, elem, le, succ
from kdrag.contrib.zf.nat import elem_succ_self
from kdrag.contrib.zf.ordinal import is_ordinal, is_ordinal_succ
from kdrag.contrib.zf.ordset import (
    is_ordinal_bigunion,
    le_bigunion,
    ordinal_not_elem_self,
)

A, C, x = Consts("A C x", ZFSet)
l = kd.Lemma(Not(Exists(C, ForAll(A, is_ordinal(A), elem(A, C)))))
l.intro()
C0, _ = l.obtain(-1)
O = zf.sep(C0, Lambda(x, is_ordinal(x)))
l.have(ForAll(x, elem(x, O), is_ordinal(x)))
x0 = l.fix()
l.intro()
l.rw(zf.elem_sep, at=-1)
l.simp(at=-1)
l.auto()
U = bigunion(O)
l.have(is_ordinal(U), by=[is_ordinal_bigunion(O)])
l.have(is_ordinal(succ(U)), by=[is_ordinal_succ(U)])
l.have(elem(succ(U), O))
l.rw(zf.elem_sep)
l.simp()
l.auto()
l.have(succ(U) <= U, by=[le_bigunion(O, succ(U))])
try:
    l.have(elem(U, U), by=[le.defn(succ(U), U), elem_succ_self(U)])
    print("proved")
except Exception as e:
    c = e
    while c is not None:
        if type(c).__name__ == "SolverFailure":
            shutil.copy(c.args[-1], "bf_export.smt2")
            print("failed:", c.args[-2])
            break
        c = c.__cause__ or c.__context__
