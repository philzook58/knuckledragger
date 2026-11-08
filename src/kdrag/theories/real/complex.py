import kdrag as kd
from kdrag import ComplexSort, Inductive, QForAll, define, prove
from kdrag.smt import Consts, ForAll, Reals
import kdrag.theories.real as real

C = ComplexSort()
z, w, u, z1, z2 = Consts("z w u z1 z2", C)
add = kd.complex_add
mul = kd.complex_mul
div = kd.complex_div
conj = define("conj", [z], C.C(z.re, -z.im))

C0 = C.C(0, 0)
zero = C0
C1 = C.C(1, 0)
one = C1
Ci = C.C(0, 1)
j = Ci

add_zero = prove(ForAll([z], z + C0 == z), by=[add.defn])
mul_zero = prove(ForAll([z], z * C0 == C0), by=[mul.defn])
mul_one = prove(ForAll([z], z * C1 == z), by=[mul.defn])
add_comm = prove(ForAll([z, w], z + w == w + z), by=[add.defn])
add_assoc = prove(ForAll([z, w, u], (z + (w + u)) == ((z + w) + u)), by=[add.defn])
mul_comm = prove(ForAll([z, w], z * w == w * z), by=[mul.defn])
mul_assoc = prove(ForAll([z, w, u], (z * (w * u)) == ((z * w) * u)), by=[mul.defn])

# unstable perfoamnce.
# mul_div = kd.prove(ForAll([z,w], Implies(w != C0, z == z * w / w)), by=[div.defn, mul.defn], timeout=1000)
##mul_div = Calc()
# div_one = kd.prove(smt.ForAll([z], z / C1 == z), by=[div.defn])
# div_inv = kd.prove(
#    smt.ForAll([z], smt.Implies(z != C0, z / z == C1)), by=[div.defn], admit=True
# )

# inv = kd.define("inv", [z], )

# conjugate
# polar
norm2 = define("C.norm2", [z], z * conj(z))

t, s = Reals("t s")
expi = define("expi", [t], C.C(real.cos(t), real.sin(t)))

# expi_mul = kd.prove(
#   smt.ForAll([t, s], expi(t) * expi(s) == expi(t + s)),
#    by=[expi.defn, mul.defn, real.sin_add, real.cos_add],
# )

c = kd.tactics.Calc([t, s], expi(t) * expi(s))
c.eq(C.C(real.cos(t), real.sin(t)) * C.C(real.cos(s), real.sin(s)), by=[expi.defn])
c.eq(
    C.C(
        real.cos(t) * real.cos(s) - real.sin(t) * real.sin(s),
        real.cos(t) * real.sin(s) + real.sin(t) * real.cos(s),
    ),
    by=[mul.defn],
)
_1 = c.qed()
# c.eq(C.C(real.cos(t + s), real.sin(t + s)), by=[real.cos_add, real.sin_add])
c = kd.tactics.Calc([t, s], C.C(real.cos(t + s), real.sin(t + s)))
c.eq(expi(t + s), by=[expi.defn])
expi_mul = c.qed()
_2 = c.qed()

_3 = prove(
    QForAll(
        [t, s],
        C.C(
            real.cos(t) * real.cos(s) - real.sin(t) * real.sin(s),
            real.cos(t) * real.sin(s) + real.sin(t) * real.cos(s),
        )
        == C.C(real.cos(t + s), real.sin(t + s)),
    ),
    by=[real.cos_add, real.sin_add],
)
expi_mul = prove(
    QForAll([t, s], expi(t) * expi(s) == expi(t + s)), by=[_1, _2, _3], admit=True
)

RSphere = Inductive("RSphere")
RSphere.declare("Finite", ("val", C))
RSphere.declare("Inf")
RSphere.create()

# mobius
# conformal
