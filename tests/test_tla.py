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

------------------------------

THEOREM  HC => []HCini

==========================
"""

hour_cfg = r"""
SPECIFICATION HC
   \* This statement tells TLC that HC is the specification that it
   \* should check.

INVARIANT HCini
"""

def test_tla_to_xml():
    with open("/tmp/HourClock.tla", "w") as f:
        f.write(hour_clock)
    xml = tla.tla_to_xml("/tmp/HourClock.tla")
    mod = tla.Module.of_file("/tmp/HourClock.tla")
    assert mod.name == "HourClock"
    assert mod.variables == ["hr"]
    assert list(mod.definitions.keys()) == ["HCini", "HCnxt", "HC"]
    assert mod.theorems == [tla.App("=>", [tla.App("HC", []), tla.App("[]", [tla.App("HCini", [])])])]
    hr, hr1 = smt.Ints("hr hr'")
    decls = {"hr": hr}
    assert mod.action("HCini", decls).sort() == smt.BoolSort()
    assert mod.action("HCnxt", decls).eq(hr1 == smt.If(hr == 12, 1, hr + 1))
    assert mod.infer_sorts(typeok="HCini") == decls
    with open("/tmp/HourClock.cfg", "w") as f:
        f.write(hour_cfg)
    tla.check("/tmp/HourClock.tla")



mytest = r"""
---- MODULE MyTest ----
VARIABLES is_unique
VARIABLES biz

TypeInvariant == /\ is_unique \in BOOLEAN

==========================
"""

def test_tla_mytest():
    with open("/tmp/MyTest.tla", "w") as f:
        f.write(mytest)
    mod = tla.Module.of_file("/tmp/MyTest.tla")
    assert mod.name == "MyTest"
    assert mod.variables == ["biz", "is_unique"]
    assert list(mod.definitions.keys()) == ["TypeInvariant"]
    assert mod.theorems == []
    decls = mod.infer_sorts(typeok="TypeInvariant")
    assert decls == {"is_unique": smt.Const("is_unique", smt.BoolSort())}
    assert mod.action("TypeInvariant", decls).sort() == smt.BoolSort()