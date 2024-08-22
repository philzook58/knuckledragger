import knuckledragger as kd
import knuckledragger.smt as smt

C = kd.notation.Record("C", ("re", smt.RealSort()), ("im", smt.RealSort()))

z, w, u, z1, z2 = smt.Consts("z w u z1 z2", C)
add = kd.define("add", [z1, z2], C.mk(z1.re + z2.re, z1.im + z2.im))
kd.notation.add.register(C, add)
mul = kd.define(
    "mul", [z1, z2], C.mk(z1.re * z2.re - z1.im * z2.im, z1.re * z2.im + z1.im * z2.re)
)
kd.notation.mul.register(C, mul)
conj = kd.define("conj", [z], C.mk(z.re, -z.im))


div = kd.notation.div.define(
    [z1, z2],
    C.mk(
        (z1.re * z2.re + z1.im * z2.im) / (z2.re**2 + z2.im**2),
        (z1.im * z2.re - z1.re * z2.im) / (z2.re**2 + z2.im**2),
    ),
)

C0 = C.mk(0, 0)
C1 = C.mk(1, 0)
Ci = C.mk(0, 1)

add_zero = kd.lemma(smt.ForAll([z], z + C0 == z), by=[add.defn])
mul_zero = kd.lemma(smt.ForAll([z], z * C0 == C0), by=[mul.defn])
mul_one = kd.lemma(smt.ForAll([z], z * C1 == z), by=[mul.defn])
add_comm = kd.lemma(smt.ForAll([z, w], z + w == w + z), by=[add.defn])
add_assoc = kd.lemma(
    smt.ForAll([z, w, u], (z + (w + u)) == ((z + w) + u)), by=[add.defn]
)
mul_comm = kd.lemma(smt.ForAll([z, w], z * w == w * z), by=[mul.defn])

# unstable perfoamnce.
# mul_div = kd.lemma(ForAll([z,w], Implies(w != C0, z == z * w / w)), by=[div.defn, mul.defn], timeout=1000)
##mul_div = Calc()
# div_one = kd.lemma(smt.ForAll([z], z / C1 == z), by=[div.defn])
# div_inv = kd.lemma(
#    smt.ForAll([z], smt.Implies(z != C0, z / z == C1)), by=[div.defn], admit=True
# )

# inv = kd.define("inv", [z], )

# conjugate
# polar
norm2 = kd.define("norm2", [z], z * conj(z))
