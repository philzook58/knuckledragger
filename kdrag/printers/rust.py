import kdrag.smt as smt
import subprocess
import importlib
import os


def of_sort(s: smt.SortRef):
    if s == smt.BoolSort():
        return "bool"
    if isinstance(s, smt.BitVecSortRef):
        if s.size() in [8, 16, 32, 64]:
            return f"u{s.size()}"
        else:
            raise NotImplementedError("No support for arbitrary C int sizes", s.size())
    else:
        raise NotImplementedError(f"Cannot convert {s} to C type")


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
