import kdrag as kd
from kdrag import QForAll, Struct, define, prove
from kdrag.smt import (
    ArraySort,
    Consts,
    Function,
    If,
    IntSort,
    Ints,
    K,
    Lambda,
    RealSort,
    RealVal,
)
import kdrag.theories.seq as seq

NDArray = Struct(
    "NDArray",
    ("shape", seq.Seq(IntSort())),
    ("data", ArraySort(IntSort(), RealSort())),
)

n, m, k = Ints("n m k")

zeros = define("zero", [n], NDArray(seq.Unit(n), K(IntSort(), RealVal(0))))
ones = define("ones", [n], NDArray(seq.Unit(n), K(IntSort(), RealVal(1))))

u, v, w = Consts("u v w", NDArray)
add_undef = Function("add_undef", NDArray, NDArray, NDArray)
add = kd.notation.add.define(
    [u, v],
    If(
        u.shape == v.shape,  # broadcasting rules are actually more complicated
        NDArray(u.shape, Lambda(k, u.data[k] + v.data[k])),
        add_undef(u, v),
    ),
)
add_comm = prove(
    QForAll([u, v], u.shape == v.shape, add(u, v) == add(v, u)), by=[add.defn]
)
