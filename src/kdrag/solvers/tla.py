"""
Automatically downloads tla2tools.jar
"""
import kdrag.solvers
import subprocess
import xml.etree.ElementTree as ET
from dataclasses import dataclass
import kdrag.smt as smt
import operator

kdrag.solvers.download("https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar", "tla2tools.jar", "237332bdcc79a35c7d26efa7b82c77c85c2744591c5598673a8a45085ff2a4fb")


def check(filename : str):
    """
    Run the model checker on a tla file. Returns the stdout of the model checker.
    """
    return subprocess.run(
        [
            "java",
            "-cp",
            kdrag.solvers.binpath("tla2tools.jar"),
            "tlc2.TLC",
            filename,
        ],
        check=True,
        capture_output=True,
    ).stdout

def pluscal_translate(filename : str) -> bytes:
    """
    Run the pluscal translator on a tla file. Returns the stdout of the translator.
    """
    return subprocess.run(
        [
            "java",
            "-cp",
            kdrag.solvers.binpath("tla2tools.jar"),
            "pcal.trans",
            filename,
        ],
        check=True,
        capture_output=True,
    ).stdout

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
    "Untyped Ast for expressions"
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
    theorems : list[App]
    # assumes, constants, extends

    def action(self, actname : str, decls: dict[str, smt.FuncDeclRef | smt.ExprRef]) -> smt.ExprRef:
        """
        Return the action of the module as an smt expression. These are expressions that may involve primed variables, 
        but do not involve other temporal operators.
        """
        return to_smt(self.definitions[actname], decls, sort=smt.BoolSort())
    
    def behavior(self, name : str, decls : dict[str, smt.FuncDeclRef | smt.ExprRef]) -> smt.ExprRef:
        """
        Return a useful smt form of statements that involve non trivial temporal operators
        """
        raise NotImplementedError("behavior", name, decls)
    
    def infer_sorts(self, typeok="TypeOk") -> dict[str, smt.ExprRef]:
        todo = [self.definitions[typeok]]
        decls = {}
        while todo:
            e = todo.pop()
            match e:
                case App("\\land", args) | App("$ConjList", args):
                    todo.extend(args)
                #case App("=", [App(lhs, []), rhs]):
                #    assert lhs not in decls, f"lhs {lhs} already in decls"
                #    decls[lhs] = smt.Const(lhs, to_smt(rhs, decls).sort())
                case App("\\in", [App(lhs, []), rhs]):
                    assert lhs not in decls, f"lhs {lhs} already in decls"
                    doms = smt.domains(to_smt(rhs, decls))
                    assert len(doms) == 1, f"expected one domain for {rhs}, got {doms}"
                    decls[lhs] = smt.Const(lhs, doms[0])
                case _:
                    raise ValueError("unexpected expression in infer_sorts", e)
        return decls

    @staticmethod
    def of_file(filename) -> "Module":
        mods = ET.fromstring(tla_to_xml(filename))
        name = mods.findtext("RootModule")
        assert name is not None

        by_uid = {}
        for entry in mods.findall("context/entry"):
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
                return App(f, [] if operands is None else [expr(arg) for arg in operands])
            if node.tag.endswith("Ref"):
                return App(ref_name(node), [])
            if node.tag == "NumeralNode":
                return App(int(node.findtext("IntValue")), [])
            return App(node.findtext("uniquename") or node.tag, [])

        root = next(
            node
            for node in by_uid.values()
            if node.tag == "ModuleNode" and node.findtext("uniquename") == name
        )
        variables = []
        for ref in root.findall("OpDeclNodeRef"):
            node = by_uid.get(ref.findtext("UID"))
            if node is not None and node.findtext("./location/filename") == name:
                variables.append(node.findtext("uniquename"))

        definitions = {}
        theorems = []
        for node in by_uid.values():
            if node.findtext("./location/filename") != name:
                continue
            body = node.find("./body/*")
            if node.tag == "UserDefinedOpKind" and body is not None:
                definitions[node.findtext("uniquename")] = expr(body)
            elif node.tag == "TheoremNode" and body is not None:
                theorems.append(expr(body))

        return Module(name, variables, definitions, theorems)




binops = {
    "+": operator.add,
    "-": operator.sub,
    "*": operator.mul,
    "%" : operator.mod,

}


def to_smt(e: App, decls: dict[str, smt.FuncDeclRef | smt.ExprRef], sort=None):
    if e.f in decls:
        assert isinstance(e.f, str)
        f = decls[e.f]
        if isinstance(f, smt.FuncDeclRef):
            assert len(e.args) == f.arity()
            assert sort is None or sort == f.range()
            args = [to_smt(arg, decls, sort=f.domain(i)) for i, arg in enumerate(e.args)]
            return f(*args)
        elif isinstance(f, smt.ExprRef):
            assert not e.args
            assert sort is None or sort == f.sort()
            return f
        else:
            raise ValueError(f"decls[{e.f}] is not a FuncDeclRef or ExprRef")
    elif isinstance(e.f, int) and not e.args:
        assert sort is None or sort == smt.IntSort()
        return smt.IntVal(e.f)
    elif e.f == "\\land" or e.f == "$ConjList":
        args = [to_smt(arg, decls, sort=smt.BoolSort()) for arg in e.args]
        if len(args) == 0:
            return smt.BoolVal(True)
        elif len(args) == 1:
            return args[0]
        else:
            return smt.And(*args)
    elif e.f == "\\lor":
        assert len(e.args) >= 2
        args = [to_smt(arg, decls, sort=smt.BoolSort()) for arg in e.args]
        return smt.Or(*args)
    elif e.f == "=":
        assert len(e.args) == 2
        # maybe vice versa for sort propagation?
        rhs = to_smt(e.args[1], decls)
        lhs = to_smt(e.args[0], decls, sort=rhs.sort())
        return smt.Eq(lhs, rhs)
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
    elif e.f == "BOOLEAN":
        assert not e.args
        return smt.FullSet(smt.BoolSort())
    # These appear in spec statements
    #elif e.f == "$SquareAct":
    #    return smt.Const("$SQUAREACT TODO", smt.BoolSort())
    #elif e.f == "[]":
    #    return smt.Const("[] TODO", smt.BoolSort())
    # elif sort is not None:
    #    # fallback to uninterprted function
    #    args = [to_smt(arg, decls) for arg in e.args]
    #    f = smt.Function(e.f, *[arg.sort() for arg in args], sort)
    #    return f(*args)
    else:
        raise ValueError(f"Cannot convert {e} to smt without sort")
