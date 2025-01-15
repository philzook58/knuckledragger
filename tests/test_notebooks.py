import pytest
import nbformat
from nbclient import NotebookClient
import subprocess
import tempfile

notebooks = [
    "examples/nng.ipynb",
    "examples/soft_found/lf/Basics.ipynb",
    "examples/soft_found/lf/IndProp.ipynb",
    "examples/soft_found/lf/Imp.ipynb",
    "examples/LoVe/05_function.ipynb",
]


@pytest.mark.slow
@pytest.mark.parametrize(
    "notebook_path",
    ["tutorial.ipynb"] + notebooks,
)
def test_notebook_execution(notebook_path):
    with open(notebook_path, "r", encoding="utf-8") as f:
        nb = nbformat.read(f, as_version=4)
    nb["cells"] = [
        cell
        for cell in nb["cells"]
        if "test_skip" not in cell.get("metadata", {}).get("tags", [])
    ]
    client = NotebookClient(nb)
    client.execute()


"""
@pytest.mark.parametrize(
    "notebook_path",
    notebooks,
 )
def test_notebook_execution2():  # notebook_path):
    with tempfile.NamedTemporaryFile(suffix=".py", delete=False) as temp_output:
        result = subprocess.run(
            ["jupyter", "nbconvert", "--to", "python"]
            + notebooks
            + [
                "--execute",
                "--output",
                temp_output.name,
            ],
            capture_output=True,
            text=True,
        )
        assert result.returncode == 0, result.stderr
        # subprocess.run(["python3", temp_output.name], check=True, text=True)
        # assert result.returncode == 0, result.stderr
"""

import re


def test_readme():
    with open("README.md", "r") as file:
        content = file.read()

    # Regular expression to match Python code blocks
    python_code_blocks = re.findall(r"```python\n(.*?)```", content, re.DOTALL)

    if not python_code_blocks:
        raise ValueError("No Python code blocks found in the README.md file.")

    for i, block in enumerate(python_code_blocks, 1):
        exec(block)
