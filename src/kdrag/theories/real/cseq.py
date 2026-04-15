from kdrag import axiom, prove, Theorem, Complex, R, Z, PTheorem  # noqa: F401
from kdrag.smt import ForAll, Const, Lambda, Implies, If, Or, Consts, And, Ints  # noqa: F401
import kdrag as kd
import kdrag.smt as smt
import kdrag.theories.real.complex as complex
import kdrag.theories.real.seq as seq

CSeq = smt.ArraySort(Z, Complex)
a, b, c = Consts("a b c", CSeq)
i, j, k, n = Ints("i j k n")
add = kd.add.define([a, b], Lambda([i], a[i] + b[i]))

add_comm = prove(ForAll([a, b], a + b == b + a), by=[add.defn, complex.add_comm])
add_assoc = prove(
    ForAll([a, b, c], (a + b) + c == a + (b + c)), by=[add.defn, complex.add_assoc]
)


mul = kd.mul.define(
    [a, b],
    Lambda([i], a[i] * b[i]),
)
mul_comm = prove(ForAll([a, b], a * b == b * a), by=[mul.defn, complex.mul_comm])
mul_assoc = prove(
    ForAll([a, b, c], (a * b) * c == a * (b * c)), by=[mul.defn, complex.mul_assoc]
)

unzip = kd.define("C.unzip", [a], kd.tuple_(Lambda([i], a[i].re), Lambda([i], a[i].im)))

ab = Const("ab", kd.TupleSort(seq.RSeq, seq.RSeq))
rezip = kd.define("C.rezip", [ab], Lambda([i], Complex(ab[0][i], ab[1][i])))

rezip_unzip = prove(ForAll([a], rezip(unzip(a)) == a), by=[rezip.defn, unzip.defn])
unzip_rezip = prove(ForAll([ab], unzip(rezip(ab)) == ab), by=[rezip.defn, unzip.defn])

# Map over theorems and definitions from rseq
