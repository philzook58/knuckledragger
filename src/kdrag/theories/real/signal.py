import kdrag as kd
import kdrag.smt as smt

import kdrag.theories.real as real


RSeq = real.RSeq

a, b, c = smt.Consts("a b c", RSeq)
i, j, k = smt.Ints("i j k")
diff = kd.define("diff", [a], smt.Lambda([i], a[i + 1] - a[i]))


cumsum = smt.Function("cumsum", RSeq, RSeq)
cumsum = kd.define(
    "cumsum",
    [a],
    smt.Lambda(
        [i],
        smt.If(
            i == 0,
            a[0],
            smt.If(i > 0, cumsum(a)[i - 1] + a[i], -cumsum(a)[i + 1] - a[i]),
        ),
    ),
)

A, B, C = kd.FreshVars("A B C", RSeq)
sin = kd.define("sin", [a], smt.Map(real.sin, a))
cos = kd.define("cos", [a], smt.Map(real.cos, a))

add = kd.define("add", [a, b], smt.Map(real.add, a, b))
kd.notation.add.register(RSeq, add)
add_comm = kd.prove(
    A + B == B + A, by=[add.defn(B, A), add.defn(A, B), real.add_comm]
).forall([A, B])
add_assoc = kd.prove(
    (A + B) + C == A + (B + C),
    unfold=1,
    by=[real.add_assoc],
).forall([A, B, C])
# kd.Lemma(diff(cumsum(A)) == A)
