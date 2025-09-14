import kdrag as kd
import kdrag.smt as smt
import kdrag.theories.seq as seq

NDArray = kd.Struct(
    "NDArray",
    ("shape", seq.Seq(smt.IntSort())),
    ("data", smt.ArraySort(smt.IntSort(), smt.RealSort())),
)

n, m, k = smt.Ints("n m k")

zeros = kd.define(
    "zero", [n], NDArray(seq.Unit(n), smt.K(smt.IntSort(), smt.RealVal(0)))
)
ones = kd.define(
    "ones", [n], NDArray(seq.Unit(n), smt.K(smt.IntSort(), smt.RealVal(1)))
)

u, v, w = smt.Consts("u v w", NDArray)
add_undef = smt.Function("add_undef", NDArray, NDArray, NDArray)
add = kd.notation.add.define(
    [u, v],
    smt.If(
        u.shape == v.shape,  # broadcasting rules are actually more complicated
        NDArray(u.shape, smt.Lambda(k, u.data[k] + v.data[k])),
        add_undef(u, v),
    ),
)
add_comm = kd.prove(
    kd.QForAll([u, v], u.shape == v.shape, add(u, v) == add(v, u)), by=[add.defn]
)
