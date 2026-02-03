"""
Explorations in Synthesis
"""

import kdrag.smt as smt
import kdrag as kd
from typing import Optional


def cegis_simple(spec: smt.ExprRef) -> Optional[list[smt.ExprRef]]:
    """
    Given formula of the form exists ys, forall xs, P(xs,ys), attempt to find witness for ys.

    >>> x = smt.Const("x", smt.IntSort())
    >>> y = smt.Const("y", smt.IntSort())
    >>> assert cegis_simple(smt.Exists([y], smt.ForAll([x], x + y > x)))[0].as_long() > 0
    >>> z = smt.Const("z", smt.IntSort())
    >>> assert cegis_simple(smt.Exists([y], smt.ForAll([x], smt.And(y <= 0, x + y > x)))) is None
    """
    # smt.Exists([y], smt.ForAll([x], x + y > 0)) This won't solve. There isn't a solution.
    # receive formula of the form exists y, forall x, P(x,y)
    assert isinstance(spec, kd.smt.QuantifierRef) and spec.is_exists()
    evs, body = kd.utils.open_binder(spec)
    assert isinstance(body, kd.smt.QuantifierRef) and body.is_forall()
    avs, body = kd.utils.open_binder(body)
    synth = smt.Solver()
    synth.add(
        smt.FreshConst(e.sort()) == e for e in evs
    )  # seed solver to give e values
    while True:
        res = synth.check()  # find candidate e values
        if res == smt.unsat:
            return None
        elif res == smt.sat:
            m = synth.model()
            # verify
            verif = smt.Solver()
            verif.add([smt.Eq(e, m.eval(e)) for e in evs])  # or smt.substitute
            verif.add(smt.Not(body))  # seek counterexample
            res2 = verif.check()
            if res2 == smt.unsat:  # success!
                return [m.eval(e) for e in evs]
            elif res2 == smt.sat:
                m2 = verif.model()
                # add counterexample to synthesizer
                synth.add(smt.substitute(body, [(a, m2.eval(a)) for a in avs]))
        else:
            raise Exception("Unknown result from solver", res)


"""
Top down
Bottom up / Contextual compression
Use hypothesis
Term enumeration
Houdini
Spacer / CHC
Fitting
LLM
Hierasynth
Portfolio
"""
