import kdrag as kd
import kdrag.smt as smt
# https://plato.stanford.edu/Entries/logic-intuitionistic/#FormSystMathMath

# def modus(A : smt.BoolRef, AB : smt.BoolRef) -> kd.Proof:
#    return kd.axiom(smt.Implies(A, smt.Implies(AB, A)))

"""
Prop = smt.DeclareSort("Prop")
A, B = smt.Consts("A B", Prop)
Implies = smt.Function("Implies", Prop, Prop, Prop)
And = smt.Function("And", Prop, Prop, Prop)
Or = smt.Function("Or", Prop, Prop, Prop)
Not = smt.Function("Not", Prop, Prop)
modus = kd.axiom(kd.QForAll([A, B], Implies(A, Implies(A, B), B)))


"""
