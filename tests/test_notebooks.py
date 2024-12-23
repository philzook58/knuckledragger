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
