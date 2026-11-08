from kdrag.smt import BoolSort, Consts, DeclareSort, ForAll, Function
import kdrag as kd
from kdrag import QForAll, axiom

Ob = DeclareSort("Ob")
a, b, c, d = Consts("a b c d", Ob)

Arr = DeclareSort("Arr")
f, g, h, k = Consts("f g h k", Arr)

dom = Function("dom", Arr, Ob)
cod = Function("cod", Arr, Ob)

# not all arrow expressions are well formed.
wf = Function("wf", Arr, BoolSort())
kd.notation.wf.register(Arr, wf)

comp = Function("comp", Arr, Arr, Arr)
kd.notation.matmul.register(Arr, comp)
wf_comp = axiom(QForAll([f, g], cod(g) == dom(f), wf(f @ g)))

id = Function("id", Ob, Arr)
wf_id = axiom(ForAll([a], wf(id(a))))
