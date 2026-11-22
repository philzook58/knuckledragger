"""Editable JupyterLite REPL cells that replay knuckledragger theorems.

Free of Sphinx imports so `tools/check_lite_cells.py` can run the same cells
under Pyodide.
"""

import ast
import re
from pathlib import Path
from types import ModuleType
from urllib.parse import urlencode

INSTALL = "%pip install -q --no-deps knuckledragger z3-solver lark graphviz"
HEADER = [
    "# Shift+Enter to run. Python runs in your browser via Pyodide.",
    "# The first run installs knuckledragger and z3, which takes a few seconds.",
]
SKIP_FILE = Path(__file__).with_name("lite_skip.txt")


def _is_theorem(decorator: ast.expr) -> bool:
    f = decorator.func if isinstance(decorator, ast.Call) else decorator
    return (isinstance(f, ast.Name) and f.id == "Theorem") or (
        isinstance(f, ast.Attribute) and f.attr == "Theorem"
    )


def stepping_source(stmt: ast.stmt, source_lines: list[str]) -> str | None:
    """Rewrite a `@Theorem` proof for stepping through in a REPL.

    `Theorem` becomes `PTheorem`, which prints the next goal instead of failing, and
    a `return` goes before the first tactic; moving it down walks through the proof.
    Returns None for anything else.
    """
    if not isinstance(stmt, ast.FunctionDef) or not any(
        map(_is_theorem, stmt.decorator_list)
    ):
        return None
    body = stmt.body
    if isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant):
        body = body[1:]  # keep the docstring
    if not body or body[0].lineno == stmt.lineno:
        return None
    start = min(d.lineno for d in stmt.decorator_list)
    head = source_lines[start - 1 : body[0].lineno - 1]
    for d in filter(_is_theorem, stmt.decorator_list):
        i, c = d.lineno - start, d.col_offset
        head[i] = head[i][:c] + head[i][c:].replace("Theorem", "PTheorem", 1)
    indent = " " * body[0].col_offset
    stop = indent + "return  # move down (Alt+Down) to step through the proof"
    return "\n".join(head + [stop] + source_lines[body[0].lineno - 1 : stmt.end_lineno])


class Definitions:
    """Top-level definitions of a module's source: line, source, and stepping form."""

    def __init__(self, module: ModuleType):
        self.module = module
        text = Path(module.__file__).read_text()
        source_lines = text.splitlines()
        self.lines: dict[str, int] = {}
        self.source: dict[str, str] = {}  # decorators included
        self.stepping: dict[str, str] = {}
        for stmt in ast.parse(text).body:
            if isinstance(stmt, ast.FunctionDef):
                names = [stmt.name]
            elif isinstance(stmt, ast.Assign):
                names = [t.id for t in stmt.targets if isinstance(t, ast.Name)]
            elif isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
                names = [stmt.target.id]
            else:
                continue
            start = min(
                [stmt.lineno] + [d.lineno for d in getattr(stmt, "decorator_list", [])]
            )
            step = stepping_source(stmt, source_lines)
            for n in names:
                self.lines[n] = stmt.lineno
                self.source[n] = "\n".join(source_lines[start - 1 : stmt.end_lineno])
                if step is not None:
                    self.stepping[n] = step

    def cell(self, name: str, stepping=True) -> str:
        """Cell code that imports the module and replays theorem `name`.

        The cell star-imports `kdrag.all` and then the module, plus any private
        (underscore) names the proof uses, which `import *` skips. Proofs written with
        `@Theorem` come in their `stepping_source` form unless `stepping` is False.
        """
        module_name = self.module.__name__
        src = self.source.get(name, "")
        private = sorted(
            {n for n in re.findall(r"\b_\w+", src) if n in vars(self.module)}
        )
        step = self.stepping.get(name) if stepping else None
        return "\n".join(
            [
                *HEADER,
                INSTALL,
                "from kdrag.all import *",
                f"from {module_name} import *",
                *([f"from {module_name} import {', '.join(private)}"] if private else []),
                "",
                *([step or src] if step or src else []),
                *([] if step else [name]),
            ]
        )


def repl_url(base: str, code: str) -> str:
    """JupyterLite REPL link that leaves `code` editable in the prompt."""
    query = [
        ("kernel", "python"),
        ("execute", "0"),  # leave the code in the prompt, editable
        ("clearCodeContentOnExecute", "0"),  # and keep it there after running
        ("code", code),
    ]
    return f"{base}/repl/index.html?{urlencode(query)}"


def skipped() -> set[str]:
    """Theorems and modules whose cells fail under Pyodide; see `SKIP_FILE`."""
    if not SKIP_FILE.exists():
        return set()
    lines = (line.split("#")[0].strip() for line in SKIP_FILE.read_text().splitlines())
    return {line for line in lines if line}
