"""
Automatically downloads tla2tools.jar
"""
import kdrag.solvers
import subprocess
import xml.etree.ElementTree as ET
from dataclasses import dataclass
import kdrag.smt as smt

kdrag.solvers.download("https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar", "tla2tools.jar", "237332bdcc79a35c7d26efa7b82c77c85c2744591c5598673a8a45085ff2a4fb")


def tla_to_xml(filename):
    """
    Convert tla file to xml output
    """
    # https://github.com/tlaplus/tlaplus/blob/master/tlatools/org.lamport.tlatools/src/tla2sany/xml/sany.xsd
    return subprocess.run(
        [
            "java",
            "-cp",
            kdrag.solvers.binpath("tla2tools.jar"),
            "tla2sany.xml.XMLExporter",
            "-o",
            filename,
        ],
        check=True,
        capture_output=True,
    ).stdout



@dataclass
class App:
    f: object
    args: list["App"]

    def __repr__(self):
        if not self.args:
            return f"{self.f}"
        else:
            return f"{self.f}({', '.join(map(str, self.args))})"
        
@dataclass
class Module:
    name : str
    variables : list[str]
    definitions : dict[str, App]

    @staticmethod
    def of_file(self, filename): ...

def tla_exprs(filename) -> dict[str, App]:
    mods = ET.fromstring(tla_to_xml(filename))

    by_uid = {}
    entries = mods.findall("context/entry")
    assert entries is not None, "No context entries found in XML output"
    for entry in entries:
        uid = entry.findtext("UID")
        node = next((c for c in entry if c.tag != "UID"), None)
        if uid is not None and node is not None:
            by_uid[uid] = node

    def ref_name(ref):
        uid = ref.findtext("UID")
        node = by_uid.get(uid)
        if node is None:
            return f"UID:{uid}"
        return node.findtext("uniquename") or node.tag

    def expr(node):
        if node.tag == "OpApplNode":
            ref = next(iter(node.find("operator")), None)
            f = ref_name(ref) if ref is not None else node.tag
            operands = node.find("operands")
            args = [] if operands is None else [expr(arg) for arg in operands]
            return App(f, args)
        if node.tag.endswith("Ref"):
            return App(ref_name(node), [])
        if node.tag == "NumeralNode":
            return App(int(node.findtext("IntValue")), [])
        return App(node.findtext("uniquename") or node.tag, [])

    res = {}
    for node in by_uid.values():
        if node.tag != "UserDefinedOpKind":
            continue
        if node.findtext("./location/filename") != mods.findtext("RootModule"):
            continue
        body = node.find("./body/*")
        if body is not None:
            res[node.findtext("uniquename")] = expr(body)
    return res


def to_smt(e: App, decls: dict[object, smt.FuncDeclRef], sort=None):
    if e.f in decls:
        f = decls[e.f]
        assert len(e.args) == f.arity()
        assert sort is None or sort == f.range()
        args = [to_smt(arg, decls, sort=f.domain(i)) for i, arg in enumerate(e.args)]
        return f(*args)
    elif isinstance(e.f, int) and not e.args:
        assert sort is None or sort == smt.IntSort()
        return smt.IntVal(e.f)
    elif e.f == "\\land":
        assert len(e.args) >= 2
        args = [to_smt(arg, decls, sort=smt.BoolSort()) for arg in e.args]
        return smt.And(*args)
    elif e.f == "\\lor":
        assert len(e.args) >= 2
        args = [to_smt(arg, decls, sort=smt.BoolSort()) for arg in e.args]
        return smt.Or(*args)
    elif e.f == "=":
        assert len(e.args) == 2
        args = [to_smt(arg, decls) for arg in e.args]
        return smt.Eq(args[0], args[1])
    elif e.f == "..":
        assert len(e.args) == 2
        args = [to_smt(arg, decls, sort=smt.IntSort()) for arg in e.args]
        x = smt.FreshConst(smt.IntSort(), prefix="x")
        return smt.Lambda(x, smt.And(args[0] <= x, x <= args[1]))
    elif e.f == "\\in":
        x = to_smt(e.args[0], decls)
        s = to_smt(e.args[1], decls, sort=smt.SetSort(x.sort()))
        return smt.IsMember(x, s)
    elif e.f == "'":
        assert len(e.args) == 1
        x = to_smt(e.args[0], decls, sort=sort)
        return smt.Const(x.decl().name() + "'", x.sort())
    elif e.f == "$IfThenElse":
        assert len(e.args) == 3
        cond = to_smt(e.args[0], decls, sort=smt.BoolSort())
        then = to_smt(e.args[1], decls, sort=sort)
        else_ = to_smt(e.args[2], decls, sort=sort)
        return smt.If(cond, then, else_)
    elif e.f == "+":
        assert len(e.args) == 2
        args = [to_smt(arg, decls, sort=sort) for arg in e.args]
        return args[0] + args[1]
    # These appear in spec statements
    elif e.f == "$SquareAct":
        return smt.Const("$SQUAREACT TODO", smt.BoolSort())
    elif e.f == "[]":
        return smt.Const("[] TODO", smt.BoolSort())
    # elif sort is not None:
    #    # fallback to uninterprted function
    #    args = [to_smt(arg, decls) for arg in e.args]
    #    f = smt.Function(e.f, *[arg.sort() for arg in args], sort)
    #    return f(*args)
    else:
        raise ValueError(f"Cannot convert {e} to smt without sort")