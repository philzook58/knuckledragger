import pytest
import nbformat
from nbclient import NotebookClient


@pytest.mark.parametrize("notebook_path", ["tutorial.ipynb", "examples/nng.ipynb"])
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
