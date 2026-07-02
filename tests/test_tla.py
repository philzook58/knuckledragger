import kdrag.solvers.tla as tla
import kdrag.smt as smt
hour_clock = r"""
---- MODULE HourClock ----
EXTENDS Naturals

VARIABLE hr

HCini == hr \in (1 .. 12)

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1
          (* Alternately expressed as: hr' = (hr % 12) + 1 *)

HC == HCini /\ [][HCnxt]_hr
==========================
"""

def test_tla_to_xml():
    with open("/tmp/HourClock.tla", "w") as f:
        f.write(hour_clock)
    xml = tla.tla_to_xml("/tmp/HourClock.tla")
    exprs = tla.tla_exprs("/tmp/HourClock.tla")
    mod = tla.Module.of_file("/tmp/HourClock.tla")
    assert mod.name == "HourClock"
    assert mod.variables == ["hr"]
    assert mod.definitions.keys() == ["HCini", "HCnxt", "HC"]
    decls : dict[object, smt.FuncDeclRef] = {"hr": smt.Function("hr", smt.IntSort())}
    for name, e in exprs.items():
        print(f"{name} = {e}")
        ze = tla.to_smt(e, decls, sort=None)
        print(decls)
        decls[name] = smt.Function(name, ze.sort())
        print(ze)
