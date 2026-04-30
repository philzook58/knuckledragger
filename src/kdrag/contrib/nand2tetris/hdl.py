from kdrag import axiom, prove, Theorem, define, symdef  # noqa: F401
from kdrag.smt import (
    ForAll,
    Exists,
    Implies,
    And,
    Or,
    Not,
    If,
    IntVal,
    BitVecSort,
    K,
    BoolVal,
    DatatypeRef,
    BitVecs,
    Extract,
    Concat,
)  # noqa: F401

BV1 = BitVecSort(1)
BV2 = BitVecSort(2)
BV4 = BitVecSort(4)
BV8 = BitVecSort(8)
BV16 = BitVecSort(16)

x, y, z = BitVecs("x y z", 1)


@symdef
def nand1(x: BV1, y: BV1) -> BV1:
    return ~(x & y)


"""
@symdef
def nand_cases(x: BV1, y: BV1) -> BV1:
    match x, y:
        case 0, 0:
            return 1
        case 0, 1:
            return 1
        case 1, 0:
            return 1
        case 1, 1:
            return 0
"""


@symdef
def not1(x: BV1) -> BV1:
    return nand1(x, x)


not1_not = prove(ForAll([x], not1(x) == ~x), by=[not1.defn, nand1.defn])


@symdef
def and1(x: BV1, y: BV1) -> BV1:
    return not1(nand1(x, y))


and1_and = prove(
    ForAll([x, y], and1(x, y) == x & y), by=[and1.defn, not1_not, nand1.defn]
)


@symdef
def or1(x: BV1, y: BV1) -> BV1:
    return nand1(not1(x), not1(y))


myor_or = prove(ForAll([x, y], or1(x, y) == x | y), by=[or1.defn, not1_not, nand1.defn])


x, y = BitVecs("x y", 2)
nand2 = define(
    "nand2",
    [x, y],
    Concat(
        nand1(Extract(1, 1, x), Extract(1, 1, y)),
        nand1(Extract(0, 0, x), Extract(0, 0, y)),
    ),
)

not2 = define("not2", [x], Concat(not1(Extract(1, 1, x)), not1(Extract(0, 0, x))))
not2_not = prove(ForAll(x, not2(x) == ~x), by=[not2.defn, not1_not])


and2 = define(
    "and2",
    [x, y],
    Concat(
        and1(Extract(1, 1, x), Extract(1, 1, y)),
        and1(Extract(0, 0, x), Extract(0, 0, y)),
    ),
)
and2_and = prove(ForAll([x, y], and2(x, y) == x & y), by=[and2.defn, and1_and])

or2 = define(
    "or2",
    [x, y],
    Concat(
        or1(Extract(1, 1, x), Extract(1, 1, y)),
        or1(Extract(0, 0, x), Extract(0, 0, y)),
    ),
)
or2_or = prove(ForAll([x, y], or2(x, y) == x | y), by=[or2.defn, myor_or])
