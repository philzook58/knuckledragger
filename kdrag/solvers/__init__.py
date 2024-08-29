import kdrag as kd
import kdrag.smt as smt
import subprocess
import os


def binpath(cmd):
    return os.path.join(os.path.dirname(__file__), cmd)


def run(cmd, args, **kwargs):
    cmd = [binpath(cmd)] + args
    return subprocess.run(cmd, **kwargs)


def smtlib_datatypes(dts: list[smt.DatatypeSortRef]) -> str:
    s = smt.Z3Solver()
    for dt in dts:
        x = smt.Const("x", dt)
        s.add(smt.Exists([x], x == x))  # trivial constraint
    return (
        s.to_smt2()
        .replace("(check-sat)", "")
        .replace(
            """; benchmark generated from python API\n(set-info :status unknown)\n""",
            "",
        )
    )


class BaseSolver:
    def __init__(self):
        self.adds = []
        self.assert_tracks = []
        self.options = {}

    def add(self, thm):
        self.adds.append(thm)

    def assert_and_track(self, thm, name):
        self.assert_tracks.append((thm, name))

    def check(self):
        raise NotImplementedError

    def unsat_core(self):
        raise NotImplementedError

    def set(self, option, value):
        self.options[option] = value


def collect_sorts(exprs):
    sorts = set()
    for thm in exprs:
        sorts.update(kd.utils.sorts(thm))
    return sorts


def collect_decls(exprs):
    decls = set()
    for thm in exprs:
        decls.update(kd.utils.decls(thm))
    return decls


class VampireSolver(BaseSolver):
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

    def __init__(self):
        super().__init__()

    def check(self):
        with open("/tmp/vampire.smt2", "w") as fp:  # tempfile.NamedTemporaryFile()
            fp.write("(set-logic ALL)\n")
            # Gather up all datatypes referenced
            sorts = set()
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
            # Declare all function symbols
            fp.write(";;declarations\n")
            for f in collect_decls(
                self.adds + [thm for thm, name in self.assert_tracks]
            ):
                if f not in predefined and f.name() not in [
                    "=",
                    "if",
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
                    "is",
                    "and",
                    "or",
                    "not",
                    "=>",
                    "Int",
                    "Real",
                    "abs",
                    "distinct",
                    "true",
                    "false",
                ]:
                    fp.write(f.sexpr())
                    fp.write("\n")
            fp.write(";;axioms\n")
            for e in self.adds:
                fp.write("(assert " + e.sexpr() + ")\n")
            for thm, name in self.assert_tracks:
                fp.write("(assert (! " + thm.sexpr() + " :named " + name + "))\n")
            fp.write("(check-sat)\n")
            fp.flush()
            # print(fp.readlines())
            cmd = [
                binpath("vampire"),
                fp.name,
                "--mode",
                "smtcomp",
                "--input_syntax",
                "smtlib2",  # "--ignore_unrecognized_logic", "on",
                "-t",
                str(self.options["timeout"] // 100) + "d",
            ]
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
        elif res == "sat":
            return smt.sat
        else:
            return smt.unknown

    def unsat_core(self):
        assert self.status == smt.unsat
        cores = (
            self.res.stdout.decode()
            .split("unsat\n")[1]
            .replace("(", "")
            .replace(")", "")
            .split()
        )
        cores = [smt.Bool(core) for core in cores]
        return cores
