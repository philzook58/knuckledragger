"""
Facilities for pretty printing and calling external solvers

To install extra solvers, run either:
```
python3 -m kdrag.solvers install # install extra solvers
```

or from project root run

```
./install.sh # install extra solvers
```

"""

import kdrag as kd
import kdrag.smt as smt
import subprocess
import os
import logging
import shutil
import re
from typing import Optional
import urllib.request
import stat
import kdrag.printers.lean as lean
import json
import hashlib
import urllib
import zipfile

logger = logging.getLogger("knuckledragger")


def binpath(cmd):
    return os.path.join(os.path.dirname(__file__), cmd)


def download(url, filename, checksum) -> bool:
    path = binpath(filename)

    def checkhash():
        with open(path, "rb") as f:
            digest = hashlib.file_digest(f, "sha256")
            return digest.hexdigest() == checksum

    if os.path.exists(path) and checkhash():
        return False
    print("Downloading", url, "to", path)
    urllib.request.urlretrieve(
        url,
        path,
    )
    if not checkhash():
        raise Exception("Checksum mismatch for downloaded file", filename)
    return True


def install_solvers2():
    solvers = [
        (
            "eprover-ho",
            "https://github.com/philzook58/eprover/releases/download/E.3.2.5-ho/eprover-ho",
        ),
        (
            "vampire",
            "https://github.com/vprover/vampire/releases/download/v4.9casc2024/vampire",
        ),
    ]
    for filename, url in solvers:
        filename = binpath(filename)
        urllib.request.urlretrieve(
            url,
            filename,
        )
        st = os.stat(filename)
        # Add execute permissions for user, group, and others
        os.chmod(filename, st.st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)


def install_solvers():
    print("Installing solvers")
    subprocess.run(["bash", binpath("install.sh")], check=True)


def run(cmd, args, **kwargs):
    cmd = [binpath(cmd)] + args
    return subprocess.run(cmd, **kwargs)


def mangle_decl(d: smt.FuncDeclRef, env=[]):
    """Mangle a declaration to a tptp name. SMTLib supports type based overloading, TPTP does not."""
    # single quoted (for operators) + underscore + hex id
    id_, name = d.get_id(), d.name()
    name = name.replace("!", "bang")
    # TODO: mangling of operators is busted
    # name = name.replace("*", "star")
    assert id_ >= 0x80000000
    if d in env:
        return name + "_" + format(id_ - 0x80000000, "x")
    else:
        return name + "_" + format(id_ - 0x80000000, "x")
        # TODO: single quote is not working.
        # return "'" + d.name() + "_" + format(id_ - 0x80000000, "x") + "'"


def expr_to_tptp(expr: smt.ExprRef, env=None, format="thf", theories=True):
    """Pretty print expr as TPTP"""
    if env is None:
        env = []
    if isinstance(expr, smt.IntNumRef):
        return str(expr.as_string())
    elif isinstance(expr, smt.QuantifierRef):
        vars, body = kd.utils.open_binder(expr)
        env = env + [v.decl() for v in vars]
        body = expr_to_tptp(body, env=env, format=format, theories=theories)
        if format == "fof":
            vs = ", ".join([mangle_decl(v.decl(), env) for v in vars])
            # type_preds = " & ".join(
            #    [
            #        f"{sort_to_tptp(v.sort())}({mangle_decl(v.decl(), env)}))"
            #        for v in vars
            #    ]
            # )
        else:
            vs = ", ".join(
                [
                    mangle_decl(v.decl(), env) + ":" + sort_to_tptp(v.sort())
                    for v in vars
                ]
            )
        if expr.is_forall():
            if format == "fof":
                # TODO: is adding type predicates necessary?
                # return f"(![{vs}] : ({type_preds}) => {body})"
                return f"(![{vs}] : {body})"
            return f"(![{vs}] : {body})"
        elif expr.is_exists():
            if format == "fof":
                # return f"(?[{vs}] : ({type_preds}) & {body})"
                return f"(?[{vs}] : {body})"
            return f"(?[{vs}] : {body})"
        elif expr.is_lambda():
            if format != "thf":
                raise Exception(
                    "Lambda not supported in tff tptp format. Try a thf solver", expr
                )
            return f"(^[{vs}] : {body})"
    assert smt.is_app(expr)
    children = [
        expr_to_tptp(c, env=env, format=format, theories=theories)
        for c in expr.children()
    ]
    head = expr.decl().name()
    if head == "true":
        return "$true"
    elif head == "false":
        return "$false"
    elif head == "and":
        return "({})".format(" & ".join(children))
    elif head == "or":
        return "({})".format(" | ".join(children))
    elif head == "=":
        return "({} = {})".format(children[0], children[1])
    elif head == "=>":
        return "({} => {})".format(children[0], children[1])
    elif head == "not":
        return "~({})".format(children[0])
    elif head == "if":
        # if thf:
        #    return "($ite @ {} @ {} @ {})".format(*children)
        # else:
        return "$ite({}, {}, {})".format(*children)
    elif head == "select":
        assert format == "thf"
        return "({} @ {})".format(*children)
    elif head == "distinct":
        if len(children) == 2:
            return "({} != {})".format(*children)
        return "$distinct({})".format(", ".join(children))

    if theories:
        if head == "<":
            return "$less({},{})".format(*children)
        elif head == "<=":
            return "$lesseq({},{})".format(*children)
        elif head == ">":
            return "$greater({},{})".format(*children)
        elif head == ">=":
            return "$greatereq({},{})".format(*children)
        elif head == "+":
            return "$sum({},{})".format(*children)
        elif head == "-":
            if len(children) == 1:
                return "$difference(0,{})".format(children[0])
            else:
                return "$difference({},{})".format(*children)
        elif head == "*":
            return "$product({},{})".format(*children)
        elif head == "/":
            return "$quotient({},{})".format(*children)
        # elif head == "^":
        #    return "$power({},{})".format(
        #        *children
        #    )  # This is not a built in tptp function though
    # default assume regular term
    head = mangle_decl(expr.decl(), env)
    if len(children) == 0:
        return head
    if format == "thf":
        return f"({head} @ {' @ '.join(children)})"
    else:
        return f"{head}({', '.join(children)})"


def sort_to_tptp(sort: smt.SortRef):
    """Pretty print sort as tptp"""
    name = sort.name()
    if name == "Int":
        return "$int"
    elif name == "Bool":
        return "$o"
    elif name == "Real":
        return "$real"
    elif isinstance(sort, smt.ArraySortRef):
        return "({} > {})".format(
            sort_to_tptp(sort.domain()), sort_to_tptp(sort.range())
        )
    else:
        return name.lower()


# Some are polymorphic so decl doesn't work
# predefined theory symbols don't need function declarations
predefined_names = [
    "=",
    "if",
    "and",
    "or",
    "not",
    "=>",
    "select",
    "store",
    "=>",
    ">",
    "<",
    ">=",
    "<=",
    "+",
    "-",
    "*",
    "/",
    # "^",
    "is",
    "Int",
    "Real",
    "abs",
    "distinct",
    "true",
    "false",
    "bvor",
    "bvand",
    "bvxor",
    "bvnot",
    "bvadd",
    "bvsub",
    "bvmul",
    "bvudiv",
    "bvurem",
    "bvshl",
    "bvlshr",
    "bvashr",
    "bvult",
    "bvule",
    "bvugt",
    "bvuge",
]


def mangle_decl_smtlib(d: smt.FuncDeclRef):
    """Mangle a declaration to remove overloading"""
    id_, name = d.get_id(), d.name()
    assert id_ >= 0x80000000
    return name + "_" + format(id_ - 0x80000000, "x")


def expr_to_smtlib(expr: smt.ExprRef):
    if isinstance(expr, smt.QuantifierRef):
        quantifier = (
            "forall" if expr.is_forall() else "exists" if expr.is_exists() else "lambda"
        )
        vs, body = kd.utils.open_binder(expr)
        vs = " ".join(
            [f"({mangle_decl_smtlib(v.decl())} {v.sort().sexpr()})" for v in vs]
        )
        # vs = " ".join(
        #    [f"({expr.var_name(i)} {expr.var_sort(i)})" for i in range(expr.num_vars())]
        # )

        return f"({quantifier} ({vs}) {expr_to_smtlib(body)})"
    elif kd.utils.is_value(expr):
        return expr.sexpr()
    elif smt.is_const(expr):
        decl = expr.decl()
        name = decl.name()
        if name in predefined_names:
            if name == "and":  # 0-arity applications
                return "true"
            elif name == "or":
                return "false"
            else:
                return expr.decl().name()
        return mangle_decl_smtlib(expr.decl())
    elif smt.is_app(expr):
        decl = expr.decl()
        name = decl.name()
        children = " ".join([expr_to_smtlib(c) for c in expr.children()])
        if name in predefined_names:
            if name == "if":
                name = "ite"
            elif name == "is":
                dt = decl.domain(0)
                assert isinstance(dt, smt.DatatypeSortRef)
                # find out which
                for i in range(dt.num_constructors()):
                    if decl == dt.recognizer(i):
                        name = f"(_ is {mangle_decl_smtlib(dt.constructor(i))})"
                        break
            return f"({name} {children})"
        else:
            return f"({mangle_decl_smtlib(decl)} {children})"
    elif smt.is_var(expr):
        assert False
    else:
        return expr.sexpr()


def funcdecl_smtlib(decl: smt.FuncDeclRef):
    dom = " ".join([(decl.domain(i).sexpr()) for i in range(decl.arity())])
    return f"(declare-fun {mangle_decl_smtlib(decl)} ({dom}) {decl.range().sexpr()})"


# TODO. We need to mangle the declarations
def smtlib_datatypes(dts: list[smt.DatatypeSortRef]) -> str:
    res = []
    for dt in dts:
        res.append(f"(declare-datatypes (({dt.name()} 0)) ((")
        for i in range(dt.num_constructors()):
            c = dt.constructor(i)
            res.append(f" ({mangle_decl_smtlib(c)}")
            for j in range(c.arity()):
                acc = dt.accessor(i, j)
                res.append(f" ({mangle_decl_smtlib(acc)} {acc.range()})")
            res.append(")")
        res.append(")))\n")
    return "".join(res)


# (declare-datatypes ((EPosReal 0)) (((real (val Real)) (inf))))


class BaseSolver:
    x, y, z = smt.Reals("x y z")
    n, m, k = smt.Ints("n m k")
    a, b, c = smt.Bools("a b c")
    predefined = [
        # smt.Function("abs", smt.RealSort(), smt.RealSort()),
        smt.And(a, b).decl(),
        smt.Or(a, b).decl(),
        smt.Not(a).decl(),
        smt.Implies(a, b).decl(),
        (n - m).decl(),
        (n + m).decl(),
        (n * m).decl(),
        (n == m).decl(),
        (n <= m).decl(),
    ]
    predefined_sorts = [
        "Int",
        "Real",
        "Bool",
    ]

    def __init__(self):
        self.adds = []
        self.assert_tracks = []
        self.options = {}
        self.res: Optional[subprocess.CompletedProcess] = None

    def add(self, thm: smt.BoolRef):
        if isinstance(thm, list):
            self.adds.extend(thm)
            return
        else:
            assert isinstance(thm, smt.BoolRef)
            self.adds.append(thm)

    def assert_and_track(self, thm: smt.BoolRef, name: str):
        assert isinstance(thm, smt.BoolRef)
        self.assert_tracks.append((thm, name))

    def check(self):
        raise NotImplementedError

    def unsat_core(self):
        raise NotImplementedError

    def proof(self) -> object:
        if self.res is None:
            raise Exception("No proof available")
        return getattr(self.res, "stdout")

    def set(self, option, value):
        self.options[option] = value

    def write_tptp(self, filename, format="thf"):
        assert format in ["thf", "tff", "fof"]
        logging.info("Writing TPTP file to %s", filename)
        with open(filename, "w") as fp:
            fp.write("% TPTP file generated by Knuckledragger\n")

            # Gather up all datatypes and function symbols
            predefined = set()

            if format != "fof":
                # Write sorts in TPTP THF format
                for sort in collect_sorts(
                    self.adds + [thm for thm, name in self.assert_tracks]
                ):
                    # Write sort declarations (only for user-defined sorts)
                    name = sort.name()
                    if name not in self.predefined_sorts:
                        if format != "fof":
                            fp.write(
                                f"{format}({name.lower()}_type, type, {sort_to_tptp(sort)} : $tType ).\n"
                            )
                    if isinstance(sort, smt.DatatypeSortRef):
                        # TODO: add constructors and injectivity axioms
                        for i in range(sort.num_constructors()):
                            predefined.add(sort.constructor(i))
                            predefined.add(sort.recognizer(i))
                            for j in range(sort.constructor(i).arity()):
                                predefined.add(sort.accessor(i, j))

                # Declare all function symbols in TPTP THF format
                fp.write("% Declarations\n")
                for f in collect_decls(
                    self.adds + [thm for thm, name in self.assert_tracks]
                ):
                    if f not in predefined and f.name() not in predefined_names:
                        if f.arity() == 0:
                            fp.write(
                                f"{format}({f.name()}_type, type, {mangle_decl(f)} : {sort_to_tptp(f.range())} ).\n"
                            )
                        else:
                            joiner = " > " if format == "thf" else " * "
                            dom_tptp = joiner.join(
                                [sort_to_tptp(f.domain(i)) for i in range(f.arity())]
                            )
                            fp.write(
                                f"{format}({f.name()}_decl, type, {mangle_decl(f)} : {dom_tptp} > {sort_to_tptp(f.range())}).\n"
                            )

            # Write axioms and assertions in TPTP THF format
            fp.write("% Axioms and assertions\n")
            for i, e in enumerate(self.adds):
                fp.write(
                    f"{format}(ax_{i}, axiom, {expr_to_tptp(e, format=format)}).\n"
                )
            for thm, name in self.assert_tracks:
                fp.write(
                    f"{format}({name}, axiom, {expr_to_tptp(thm, format=format)}).\n"
                )
            # fp.write("tff(goal, conjecture, $false).\n")

            fp.flush()

    def check_tptp_status(self, res):
        if b"SZS status Unsatisfiable" in res:
            self.status = smt.unsat
            return smt.unsat
        elif b"SZS status Satisfiable" in res:
            self.status = smt.sat
            return smt.sat
        elif b"SZS status GaveUp" in res:
            self.status = smt.unknown
            return smt.unknown
        else:
            raise Exception("Unexpected return from solver", res)

    def write_smt(self, fp):
        fp.write("(set-logic ALL)\n")
        # Gather up all datatypes referenced
        predefined = set()
        for sort in collect_sorts(
            self.adds + [thm for thm, name in self.assert_tracks]
        ):
            if isinstance(sort, smt.DatatypeSortRef):
                fp.write(smtlib_datatypes([sort]))
                for i in range(sort.num_constructors()):
                    predefined.add(sort.constructor(i))
                    predefined.add(sort.recognizer(i))
                    for j in range(sort.constructor(i).arity()):
                        predefined.add(sort.accessor(i, j))
            elif isinstance(sort, smt.ArraySortRef):
                continue
            elif sort.name() not in self.predefined_sorts:
                fp.write(f"(declare-sort {sort.name()} 0)\n")
        # Declare all function symbols
        fp.write(";;declarations\n")
        for f in collect_decls(self.adds + [thm for thm, name in self.assert_tracks]):
            if f not in predefined and f.name() not in predefined_names:
                fp.write(funcdecl_smtlib(f))
                fp.write("\n")
        fp.write(";;axioms\n")
        for e in self.adds:
            # We can't use e.sexpr() because we need to mangle overloaded names
            fp.write("(assert " + expr_to_smtlib(e) + ")\n")
        for thm, name in self.assert_tracks:
            fp.write("(assert (! " + expr_to_smtlib(thm) + " :named " + name + "))\n")


def collect_sorts(exprs):
    sorts = set()
    for thm in exprs:
        todo = list(kd.utils.sorts(thm))
        while len(todo) > 0:
            sort = todo.pop()
            if sort not in sorts:
                if isinstance(sort, smt.ArraySortRef):
                    todo.append(sort.domain())
                    todo.append(sort.range())
                else:
                    sorts.add(sort)
    return sorts


def collect_decls(exprs):
    decls = set()
    for thm in exprs:
        decls.update(kd.utils.decls(thm))
    return decls


def smt2tptp(smt_filename, outfile, format="tff"):
    constraints = smt.parse_smt2_file(smt_filename)
    solver = BaseSolver()
    for c in constraints:
        solver.add(c)
    solver.write_tptp(outfile, format=format)


def tptp2smt(tptp_filename):
    res = run(
        "TPTP4X/tptp4X", ["-f", "smt2", tptp_filename], capture_output=True, check=True
    )
    return smt.parse_smt2_string(res.stdout)


class VampireSolver(BaseSolver):
    def __init__(self):
        super().__init__()
        new = download(
            "https://github.com/vprover/vampire/releases/download/v5.0.0/vampire-Linux-X64.zip",
            "vampire.zip",
            "46154f788996c1f1881c5c7120abf3dbb569b42f6bfed3c7d5331b1be3e97b18",
        )
        if new or not os.path.exists(binpath("vampire")):
            with zipfile.ZipFile(binpath("vampire.zip"), "r") as zipf:
                zipf.extract("vampire", path=os.path.dirname(__file__))
            os.chmod(binpath("vampire"), 0o755)

    def check(self):
        with open("/tmp/vampire.smt2", "w") as fp:  # tempfile.NamedTemporaryFile()
            self.write_smt(fp)
            fp.write("(check-sat)\n")
            fp.flush()
            cmd = [
                binpath("vampire"),
                fp.name,
                "--mode",
                "smtcomp",
                "--input_syntax",
                "smtlib2",
                # "--ignore_unrecognized_logic", "on",
                # "--proof_extra" "fast" / "full"
                # "--latex_output" "/tmp/vampire.tex"
            ]
            if "timeout" in self.options:
                cmd.extend(["-t", str(self.options["timeout"] // 100) + "d"])
            if len(self.assert_tracks) > 0:
                cmd.extend(["--output_mode", "ucore"])
            else:
                cmd.extend(["--output_mode", "smtcomp"])

            self.res = subprocess.run(
                cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE
            )
        res = self.res.stdout
        if b"unsat\n" in res or b"% SZS status Unsatisfiable" in res:
            self.status = smt.unsat
            return smt.unsat
        elif b"sat\n" in res or b"% SZS status Satisfiable" in res:
            return smt.sat
        else:
            return smt.unknown

    def query(self, q):
        with open("/tmp/vampire.smt2", "w") as fp:  # tempfile.NamedTemporaryFile()
            # TODO: Since some sorts may be needed to be collected from the query, we're missing them
            # However, if you introduce new stuff in the query, that's kind of weird. Still useful possibly without fixing this.
            # self.add(smt.Not(q))
            self.write_smt(fp)
            # self.adds.pop()
            fp.write(f"(assert-not {expr_to_smtlib(q)})")
            fp.write("(check-sat)\n")
            fp.flush()
            cmd = [
                binpath("vampire"),
                fp.name,
                "--mode",
                "casc",
                "--question_answering",
                "synthesis",  # "answer_literal"
                "--proof",
                "off",
                "--input_syntax",
                "smtlib2",  # "--ignore_unrecognized_logic", "on",
            ]
            if "timeout" in self.options:
                cmd.extend(["-t", str(self.options["timeout"] // 100) + "d"])

            self.res = subprocess.run(
                cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE
            )
        res = self.res.stdout
        return [
            line for line in res.decode().splitlines() if "% SZS answers Tuple" in line
        ]

    def unsat_core(self):
        assert self.status == smt.unsat and self.res is not None
        cores = (
            self.res.stdout.decode()
            .split("unsat\n")[1]
            .replace("(", "")
            .replace(")", "")
            .split()
        )
        cores = [smt.Bool(core) for core in cores]
        return cores

    def proof(self):
        res = []
        assert self.res is not None
        # https://github.com/teorth/equational_theories/blob/main/equational_theories/Generated/VampireProven/src/vampire_proofs_cyc.py
        for eqnum, statement, reason in re.findall(
            r"(\d+)\. ([^[]+) \[([^\]]+)\]", self.res.stdout.decode()
        ):
            res.append((int(eqnum), statement, reason))  # TODO: Deeper parsing
        return res


class VampireTHFSolver(BaseSolver):
    def __init__(self):
        super().__init__()

    def check(self):
        self.write_tptp("/tmp/vampire.p")
        cmd = [
            binpath("vampire-ho"),
            "/tmp/vampire.p",
            "--mode",
            "portfolio",
            "--schedule",
            "snake_slh",
            "--input_syntax",
            "tptp",
        ]
        if "timeout" in self.options:
            cmd.extend(["-t", str(self.options["timeout"] // 100) + "d"])

        self.res = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

        return self.check_tptp_status(self.res.stdout)


class EProverTHFSolver(BaseSolver):
    def check(self):
        filename = "/tmp/eprover.p"
        self.write_tptp(filename)
        cmd = [
            binpath("eprover-ho"),
            "--auto-schedule=8",
            filename,
        ]
        if "timeout" in self.options:
            cmd.extend(["--cpu-limit=" + str(self.options["timeout"] // 1000 + 1)])
        self.res = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if len(self.res.stderr) > 0:
            raise Exception("Eprover error", self.res.stderr)
        return self.check_tptp_status(self.res.stdout)


class ZipperpositionSolver(BaseSolver):
    def __init__(self):
        super().__init__()

    def check(self):
        filename = "/tmp/zipperposition.p"
        self.write_tptp(filename)
        cmd = [
            "zipperposition",
            "--mode",
            "best",
            filename,
        ]
        if "timeout" in self.options:
            cmd.extend(["--timeout", str(self.options["timeout"] // 1000 + 1)])

        self.res = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        return self.check_tptp_status(self.res.stdout)


class LeoIIISolver(BaseSolver):
    def check(self):
        filename = "/tmp/leo3.p"
        self.write_tptp(filename)
        cmd = [
            "java",
            "-jar",
            binpath("leo3.jar"),
            filename,
        ]
        if "timeout" in self.options:
            cmd.extend(["-t", str(self.options["timeout"] // 1000 + 1)])

        self.res = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

        return self.check_tptp_status(self.res.stdout)


class TweeSolver(BaseSolver):
    def check(self):
        filename = "/tmp/twee.p"

        self.write_tptp(filename, format="tff")
        # cmd = [binpath("vampire"), "--mode", "clausify", filename]
        # with open("/tmp/twee2.p", "w") as fp:
        #    res = subprocess.run(cmd, stdout=fp, stderr=subprocess.PIPE)
        cmd = [
            binpath("twee"),
            "--tstp",
            "/tmp/twee.p",
        ]
        # if "timeout" in self.options:
        #    cmd.extend(["-t", str(self.options["timeout"] // 1000 + 1)])

        self.res = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

        return self.check_tptp_status(self.res.stdout)


class SATSolver:
    def __init__(self):
        self.G = smt.Goal()
        self.cmd = [binpath("kissat/build/kissat"), "--relaxed"]

    def add(self, clause):
        self.G.add(clause)

    def check(self, debug=False):
        t = smt.Then("simplify", "bit-blast", "tseitin-cnf")
        c = t(self.G)
        assert len(c) == 1
        with open("/tmp/sat.cnf", "w") as f:
            f.write(c[0].dimacs())
            f.flush()
        self.res = subprocess.run(self.cmd + ["/tmp/sat.cnf"], capture_output=True)
        res = self.res.stdout.decode()
        if "s SATISFIABLE" in res:
            return smt.sat
        elif "s UNSATISFIABLE" in res:
            return smt.unsat
        else:
            return smt.unknown


class NanoCopISolver(BaseSolver):
    def check(self):
        filename = "/tmp/nanocopi.p"
        self.write_tptp(filename, format="fof")
        cmd = [
            binpath("nanoCoP-i20/nanocopi.sh"),
            filename,
        ]
        if "timeout" in self.options:
            cmd.extend(str(self.options["timeout"] // 1000 + 1))

        self.res = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

        if b"intuitionistically Satisfiable" in self.res.stdout:
            return smt.sat
        elif b"intuitionistically Unsatisfiable" in self.res.stdout:
            return smt.unsat
        else:
            return smt.unknown


class MultiSolver(BaseSolver):
    solver_classes = [
        VampireTHFSolver,
        EProverTHFSolver,
        LeoIIISolver,
    ]
    if shutil.which("zipperposition") is not None:
        solver_classes.append(ZipperpositionSolver)

    def __init__(self, solvers=None, strict=False):
        super().__init__()
        if solvers is not None:
            self.solvers = solvers
        else:
            self.solvers = [s() for s in self.solver_classes]

    def add(self, thm):
        for s in self.solvers:
            s.add(thm)

    def assert_and_track(self, thm, name):
        for s in self.solvers:
            s.assert_and_track(thm, name)

    def set(self, option, value):
        for s in self.solvers:
            s.set(option, value)

    def check(self, strict=False):
        # TODO: This is working very sporadically
        """
        with concurrent.futures.ThreadPoolExecutor(
            max_workers=len(self.solvers)
        ) as executor:
                results = list(executor.map(lambda s: s.check(), self.solvers))
        """
        results = list(map(lambda s: s.check(), self.solvers))
        if smt.sat in results and smt.unsat in results:
            raise Exception(
                "Inconsistent results from solvers",
                {s.__class__.__name__: res for s, res in zip(self.solvers, results)},
            )
        if strict:
            if not all(r == results[0] for r in results):
                raise Exception(
                    "Inconsistent results from solvers",
                    {
                        s.__class__.__name__: res
                        for s, res in zip(self.solvers, results)
                    },
                )
        if smt.unsat in results:
            return smt.unsat
        elif smt.sat in results:
            return smt.sat
        else:
            return smt.unknown


class LeanSolver(BaseSolver):
    def __init__(self):
        self.imports = []
        self.tactic = "grind"  # can replace by bv_decide or even tactic script. The string is just spliced in.\
        # Lean version needs to be explicitly picked or else elan will check for version which is very slow.
        self.lean_version = "4.22.0-rc3"
        super().__init__()

    def check(self):
        with open("/tmp/test.lean", "w") as f:
            for imp in self.imports:
                f.write(f"import {imp}\n")
            f.write("set_option linter.unusedVariables false\n")  # To remove an warning
            f.write("set_option grind.warning false\n")
            predefined = set()
            # make inductive datatype definitions
            for sort in collect_sorts(
                self.adds + [thm for thm, name in self.assert_tracks]
            ):
                if isinstance(sort, smt.DatatypeSortRef):
                    f.write(lean.of_datatype(sort))
                    f.write("open " + sort.name() + "\n")
                    for n in range(sort.num_constructors()):
                        cons = sort.constructor(n)
                        predefined.add(cons)
                        for i in range(cons.arity()):
                            f.write(lean.accessor_def(sort, n, i))
                            predefined.add(sort.accessor(n, i))
                elif sort.name() not in self.predefined_sorts:
                    f.write(lean.sort_axiom(sort))
            # state axioms for all non predefined declarations
            for decl in collect_decls(
                self.adds + [thm for thm, name in self.assert_tracks]
            ):
                if decl not in predefined and decl.name() not in predefined_names:
                    f.write(lean.decl_axiom(decl))
            # Make the actual goal
            f.write("theorem mythm : Not (True ")
            for expr in self.adds + [thm for thm, name in self.assert_tracks]:
                f.write("  /\\ \n")
                f.write(lean.of_expr(expr))
            f.write(f") := by {self.tactic}\n")
            f.write("#check mythm\n")
            f.flush()
        result = subprocess.run(
            ["elan", "run", self.lean_version, "lean", "--json", "/tmp/test.lean"],
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            return smt.unknown
        else:
            result = json.loads(result.stdout)
            assert result["severity"] == "information"
            assert "mythm" in result["data"]
            return smt.unsat
