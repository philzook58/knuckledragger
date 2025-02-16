import kdrag.smt as smt
import kdrag as kd

EReal = smt.Datatype("EReal")
EReal.declare("real", ("val", smt.RealSort()))
EReal.declare("inf")
EReal.declare("neg_inf")
EReal.declare("NaN")
EReal = EReal.create()

EPosReal = smt.Datatype("EPosReal")
EPosReal.declare("real", ("val", smt.RealSort()))
EPosReal.declare("inf")
EPosReal = EPosReal.create()
x_p = smt.Const("x", EPosReal)
kd.notation.wf.define([x_p], smt.Implies(x_p.is_real, x_p.val >= 0))
