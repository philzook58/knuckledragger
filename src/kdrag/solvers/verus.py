import kdrag.solvers
import subprocess
import xml.etree.ElementTree as ET
from dataclasses import dataclass, field
import kdrag.smt as smt
import operator
import kdrag as kd
from typing import Callable
import zipfile
import os


verus_path = kdrag.solvers.binpath("verus/verus-x86-linux/verus")


def install():
    zipname = "verus-0.2026.07.12.0b42f4c-x86-linux.zip"
    kdrag.solvers.download(
        "https://github.com/verus-lang/verus/releases/download/release%2F0.2026.07.12.0b42f4c/verus-0.2026.07.12.0b42f4c-x86-linux.zip",
        zipname,
        "f6f4f5d08e07d3e1ad721d775bda5ba96b9dd0c73b48fc17f2e071866fbd01c0",
    )

    with zipfile.ZipFile(kdrag.solvers.binpath(zipname), "r") as zip_ref:
        zip_ref.extractall(kdrag.solvers.binpath("verus"))

    os.chmod(verus_path, 0o755)
    rust_verify_path = kdrag.solvers.binpath("verus/verus-x86-linux/rust_verify")
    os.chmod(rust_verify_path, 0o755)
    os.chmod(kdrag.solvers.binpath("verus/verus-x86-linux/z3"), 0o755)


install()


def run_verus(args: list[str]) -> subprocess.CompletedProcess:
    return subprocess.run(
        [verus_path] + args,
        capture_output=True,
        check=True,
    )


# There is already one in rust.py
# @dataclass
# class Module:
#    name : str


@dataclass
class TransitionSystem:
    name: str
    fields: list[smt.ExprRef]
    init: tuple[str, smt.BoolRef]
    transitions: tuple[str, smt.BoolRef]
    invariants: dict[str, smt.BoolRef] = field(default_factory=dict)
    # inductive # proofs?
