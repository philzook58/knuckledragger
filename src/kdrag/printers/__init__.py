"""
Printers for C, Rust, verilog, smtlib2, tptp, lean, etc
"""

import kdrag.smt as smt


def finsize(s: smt.SortRef):
    return s == smt.BoolSort() or isinstance(s, smt.BitVecSortRef)
