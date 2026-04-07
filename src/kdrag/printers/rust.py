import kdrag.smt as smt
import kdrag as kd
import subprocess
import importlib
import os
from dataclasses import dataclass, field
from typing import Iterable
import shutil


def mangle_name(name: str) -> str:
    """
    Mangle a name to be a valid Rust identifier
    >>> mangle_name("my-fun")
    'my_KDHYPH_fun'
    >>> mangle_name("my.fun")
    'my_KDDOT_fun'
    """
    return (
        name.replace("!", "_KDBANG_")
        .replace(".", "_KDDOT_")
        .replace("-", "_KDHYPH_")
        .replace(" ", "_")
    )


def of_sort(s: smt.SortRef) -> str:
    """

    >>> of_sort(smt.SeqSort(smt.BitVecSort(8)))
    'Seq<u8>'
    >>> of_sort(smt.IntSort())
    'int'
    >>> of_sort(smt.BoolSort())
    'bool'
    >>> of_sort(smt.ArraySort(smt.IntSort(), smt.BoolSort()))
    'Set<int>'
    """
    if s == smt.BoolSort():
        return "bool"
    elif isinstance(s, smt.BitVecSortRef):
        if s.size() in [8, 16, 32, 64]:
            return f"u{s.size()}"
        else:
            raise NotImplementedError("No support for arbitrary C int sizes", s.size())
    elif s == smt.IntSort():
        return "int"
    elif isinstance(s, smt.SeqSortRef):
        return f"Seq<{of_sort(s.basis())}>"
    elif isinstance(s, smt.ArraySortRef):
        outsort = s.range()
        if outsort == smt.BoolSort():
            return f"Set<{of_sort(s.domain())}>"
        else:
            return f"Map<{of_sort(s.domain())}, {of_sort(outsort)}>"
    elif isinstance(s, smt.DatatypeSortRef):
        if kd.is_tuple_sort(s):
            return (
                "("
                + ", ".join(
                    of_sort(s.accessor(0, i).range())
                    for i in range(s.constructor(0).arity())
                )
                + ")"
            )
        else:
            return s.name()
    else:
        raise NotImplementedError(f"Cannot convert {s} to C type")


def datatype_sort(s: smt.DatatypeSortRef) -> str:
    """
    >>> datatype_sort(kd.TupleSort(smt.IntSort(), smt.BoolSort()))
    'struct Tuple_Int_Bool { _0 : int, _1 : bool }'
    >>> datatype_sort(kd.ListSort(smt.IntSort()))
    'enum List_Int { Nil {  }, Cons { head : int, tail : List_Int } }'
    """
    enums = []
    nconstr = s.num_constructors()
    for i in range(nconstr):
        constr = s.constructor(i)
        fields = []
        for j in range(constr.arity()):
            acc = s.accessor(i, j)
            field_name = acc.name()
            field_type = of_sort(acc.range())
            fields.append(f"{field_name} : {field_type}")
        fields_str = ", ".join(fields)
        enums.append(f"{constr.name()} {{ {fields_str} }}")
    if nconstr == 1:
        assert s.name() == s.constructor(0).name()
        return "struct " + enums[0]
    return f"enum {s.name()} {{ {", ".join(enums)} }}"


def of_expr(e: smt.ExprRef) -> str:
    """
    >>> of_expr(smt.IntVal(5))
    '5'
    >>> of_expr(smt.BitVecVal(255, 8))
    '0xff'
    >>> of_expr(smt.Or(smt.BoolVal(True), smt.BoolVal(False)))
    '(true || false)'
    >>> of_expr(smt.And(smt.BoolVal(True), smt.BoolVal(False)))
    '(true && false)'
    >>> of_expr(smt.Not(smt.BoolVal(True)))
    '(!true)'
    >>> of_expr(smt.Int("x"))
    'x'
    >>> of_expr(smt.If(smt.Int("x") > 0, smt.Int("x"), -smt.Int("x")))
    '(if (x > 0) { x } else { (-x) })'
    """
    assert e.sort() != smt.RealSort(), "Real sort not supported"
    if isinstance(e, smt.QuantifierRef):
        # TODO https://verus-lang.github.io/verus/guide/forall.html
        raise NotImplementedError("Cannot convert quantifier to Rust expressions", e)
    args = list(map(of_expr, e.children()))
    if smt.is_true(e):
        return "true"
    elif smt.is_false(e):
        return "false"
    elif smt.is_int_value(e):
        return str(e)
    elif isinstance(e, smt.BitVecNumRef):
        return hex(e.as_long())
    elif smt.is_add(e):
        res = " + ".join(args)
    elif smt.is_mul(e):
        res = " * ".join(args)
    elif smt.is_or(e):
        res = " || ".join(args)
    elif smt.is_and(e):
        res = " && ".join(args)
    elif smt.is_neg(e):
        (x,) = args
        res = f"-{x}"
    elif smt.is_mod(e):
        x, y = args
        res = f"{x} % {y}"
    elif smt.is_if(e):
        x, y, z = args
        res = f"if {x} {{ {y} }} else {{ {z} }}"
    elif smt.is_not(e):
        (x,) = args
        res = f"!{x}"
    elif smt.is_implies(e):
        x, y = args
        res = f"{x} ==> {y}"
    elif smt.is_eq(e):
        x, y = args
        res = f"{x} == {y}"
    elif smt.is_le(e):
        x, y = args
        res = f"{x} <= {y}"
    elif smt.is_lt(e):
        x, y = args
        res = f"{x} < {y}"
    elif smt.is_ge(e):
        x, y = args
        res = f"{x} >= {y}"
    elif smt.is_gt(e):
        x, y = args
        res = f"{x} > {y}"
    elif smt.is_select(e):
        arr, idx = args
        if e.arg(0).sort().range() == smt.BoolSort():
            res = f"{arr}.contains({idx})"
        else:
            res = f"{arr}[{idx}]"
    elif smt.is_store(e):
        m, k, v = args
        if e.arg(0).sort().range() == smt.BoolSort():
            raise NotImplementedError("Set updates not implemented yet", e)
        else:
            return f"{m}.insert({k}, {v})"
    elif smt.is_recognizer(e):
        raise NotImplementedError("Recognizers not implemented yet", e)
    elif smt.is_accessor(e):
        if e.sort().num_constructors() == 1:
            return f"{args[0]}.{e.decl().name()}"
        else:
            raise NotImplementedError(
                "Accessors for datatypes with multiple constructors not implemented yet",
                e,
            )
    elif smt.is_K(e):
        raise NotImplementedError("Constructor applications not implemented yet", e)
    elif smt.is_map(e):
        raise NotImplementedError("Map updates not implemented yet", e)
    elif isinstance(e, smt.DatatypeRef) and smt.is_constructor(e):
        dt = e.sort()
        decl = e.decl()
        nconstr = dt.num_constructors()
        for i in range(nconstr):
            constr = dt.constructor(i)
            if decl == constr:
                assert len(args) == constr.arity()
                args = [
                    f"{dt.accessor(i, j).name()} : {arg} " for j, arg in enumerate(args)
                ]
                args_str = ", ".join(args)
                if dt.num_constructors() == 1:
                    res = f"{dt.name()} {{ {args_str} }}"
                else:
                    res = f"{dt.name()}::{constr.name()}{{{args_str}}}"
                break
        else:
            raise NotImplementedError(
                f"Constructor {e.decl()} not found in datatype {dt}", e
            )
    else:
        f = e.decl()
        name = f.name()
        if smt.is_const(e):
            return mangle_name(name)
        match name:
            case "bvadd":
                x, y = args
                res = f"{x}.wrapping_add({y})"
            case "bvsub":
                x, y = args
                res = f"{x}.wrapping_sub({y})"
            case "bvmul":
                x, y = args
                res = f"{x}.wrapping_mul({y})"
            case "bvand":
                x, y = args
                res = f"{x} & {y}"
            case "bvor":
                x, y = args
                res = f"{x} | {y}"
            case "bvnor":
                x, y = args
                res = f"!({x} | {y})"
            case "bvxor":
                x, y = args
                res = f"{x} ^ {y}"
            case "bvneg":
                raise NotImplementedError("Bitvector negation not implemented yet", e)
            case "bvshl":
                x, y = args
                res = f"{x} << {y}"
            case "bvlshr":
                x, y = args
                res = f"{x} >> {y}"
            case "bvashr":
                raise NotImplementedError(
                    "Arithmetic right shift not implemented yet", e
                )
            case "bvnot":
                (x,) = args
                res = f"!{x}"
            case "bvule":
                x, y = args
                res = f"{x} <= {y}"
            case "bvult":
                x, y = args
                res = f"{x} < {y}"
            case "bvuge":
                x, y = args
                res = f"{x} >= {y}"
            case "bvugt":
                x, y = args
                res = f"{x} > {y}"
            case "concat":
                raise NotImplementedError("Concat not implemented yet", e)
            case "extract":
                raise NotImplementedError("Extract not implemented yet", e)
            case _:
                return mangle_name(name) + "(" + ", ".join(args) + ")"
    return "(" + res + ")"


@dataclass
class VerusModule:
    name: str
    datatypes: list[smt.DatatypeSortRef] = field(default_factory=list)
    spec_funs: dict[str, tuple[list[smt.ExprRef], smt.ExprRef]] = field(
        default_factory=dict
    )
    proof_funs: dict[str, tuple[list[smt.ExprRef], smt.BoolRef]] = field(
        default_factory=dict
    )

    def to_str(self):
        out = [f"mod {self.name} {{", "use vstd::prelude::*;", "verus! {"]
        for dt in self.datatypes:
            out.append(datatype_sort(dt))
        for name, (args, body) in self.spec_funs.items():
            assert isinstance(args, Iterable)
            if not all(smt.is_const(arg) for arg in args):
                raise ValueError("Arguments are not constant", name, args)
            args_str = ", ".join(
                f"{mangle_name(arg.decl().name())}: {of_sort(arg.sort())}"
                for i, arg in enumerate(args)
            )
            ret_str = of_sort(body.sort())
            body = of_expr(body)
            out.append(f"spec fn {name}({args_str}) -> {ret_str} {{ {body} }}")
        for name, (args, body) in self.proof_funs.items():
            args_str = ", ".join(
                f"{mangle_name(str(arg))}: {of_sort(arg.sort())}"
                for i, arg in enumerate(args)
            )
            body = of_expr(body)
            out.append(f"proof fn {name}({args_str}) {{ assert({body}); }}")

        out.append("}}")
        out.append("fn main() {}")
        return "\n".join(out)

    def write(self, filename):
        """
        Write module to file
        """
        code = self.to_str()
        open(filename, "w").write(code)
        fmtcmd = shutil.which("verusfmt") or shutil.which("rustfmt")
        if fmtcmd is not None:
            subprocess.run([fmtcmd, filename], check=True)

    def add_defn(self, f: smt.FuncDeclRef):
        defn = kd.kernel.defns.get(f)
        if defn is None:
            raise ValueError(f"No definition found for function {f}")
        self.spec_funs[f.name()] = (defn.args, defn.body)

    def check(self, filename, verus_binary="verus"):
        """
        Write module to file and check with Verus
        >>> m = VerusModule("testmod")
        >>> x = smt.Int("x")
        >>> m.spec_funs["myabs"] = ([x], smt.If(x >= 0, x, -x))
        >>> myabs = smt.Function("myabs", smt.IntSort(), smt.IntSort())
        >>> m.proof_funs["myabs_nonneg"] = ([x], myabs(x) >= 0)
        """

        # >>> m.check("/tmp/verus_test.rs")
        self.write(filename)
        res = subprocess.run(
            [verus_binary, filename],
            capture_output=True,
        )
        if res.returncode != 0:
            raise RuntimeError(
                "Failed to verify Verus code", res.stdout.decode(), res.stderr.decode()
            )


default_dir = "/tmp/kdrag_rust"


def init_proj(proj_path=default_dir):
    cargofile = os.path.join(proj_path, "Cargo.toml")
    res = subprocess.run(["cargo", "init", "--lib", proj_path], capture_output=True)
    if res.returncode != 0:
        print(res.stderr.decode())
        print(res.stdout.decode())
        raise RuntimeError("Failed to initialize cargo project")
    res = subprocess.run(
        [
            "cargo",
            "add",
            "pyo3",
            "--features",
            "extension-module",
            "--manifest-path",
            cargofile,
        ],
        capture_output=True,
    )
    if res.returncode != 0:
        print(res.stderr.decode())
        print(res.stdout.decode())
        raise RuntimeError("Failed to add pyo3 dependency")


def rust_module_template(modname: str, fun_name: str, fun_code: str):
    return f"""\
use pyo3::prelude::*;
use pyo3::wrap_pyfunction;

#[pyfunction]
{fun_code}

#[pymodule]
fn {modname}(m: &Bound<'_, PyModule>) -> PyResult<()> {{
    m.add_function(wrap_pyfunction!({fun_name}, m)?)?;
    Ok(())
}}
"""


def compile_rust(fun_name, fun_code, dir=default_dir):
    mod_name = os.path.basename(dir)
    cargofile = os.path.join(dir, "Cargo.toml")
    rs_file = os.path.join(dir, "src", "lib.rs")
    with open(rs_file, "w") as f:
        f.write(rust_module_template(mod_name, fun_name, fun_code))
    # Compile Rust code into a shared object
    res = subprocess.run(["maturin", "develop", "-m", cargofile], capture_output=True)
    if res.returncode != 0:
        print(res.stderr.decode())
        print(res.stdout.decode())
        raise RuntimeError("Failed to compile Rust code")
    return importlib.import_module(mod_name)
