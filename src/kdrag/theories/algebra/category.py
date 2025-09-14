import kdrag.smt as smt
import kdrag as kd

Ob = smt.DeclareSort("Ob")
a, b, c, d = smt.Consts("a b c d", Ob)

Arr = smt.DeclareSort("Arr")
f, g, h, k = smt.Consts("f g h k", Arr)

dom = smt.Function("dom", Arr, Ob)
cod = smt.Function("cod", Arr, Ob)

# not all arrow expressions are well formed.
wf = smt.Function("wf", Arr, smt.BoolSort())
kd.notation.wf.register(Arr, wf)

comp = smt.Function("comp", Arr, Arr, Arr)
kd.notation.matmul.register(Arr, comp)
wf_comp = kd.axiom(kd.QForAll([f, g], cod(g) == dom(f), wf(f @ g)))

id = smt.Function("id", Ob, Arr)
wf_id = kd.axiom(smt.ForAll([a], wf(id(a))))
