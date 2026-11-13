# Configuration file for the Sphinx documentation builder.
#
# For the full list of built-in configuration values, see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html
import sys
from pathlib import Path
# -- Project information -----------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#project-information

project = "knuckledragger"
copyright = "2024, Philip Zucker"
author = "Philip Zucker"
release = "0.1"

# -- General configuration ---------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#general-configuration


sys.path.insert(0, str(Path(__file__).resolve().parent))

extensions = [
    "sphinx.ext.duration",
    "sphinx.ext.doctest",
    "sphinx.ext.autodoc",
    "sphinx.ext.napoleon",
    "myst_parser",
]

autodoc_default_options = {
    "members": True,
    "undoc-members": True,  # Include undocumented members
    "inherited-members": True,
    "show-inheritance": True,
}
autodoc_typehints = "both"
# Run the explicit page examples through Sphinx. API docstrings run under pytest.
doctest_test_doctest_blocks = ""


templates_path = ["_templates"]
exclude_patterns = ["_build", "_autosummary", "Thumbs.db", ".DS_Store"]

# Napoleon settings
napoleon_google_docstring = True
napoleon_numpy_docstring = True
napoleon_include_init_with_doc = False
napoleon_include_private_with_doc = False
napoleon_include_special_with_doc = True
napoleon_use_admonition_for_examples = False
napoleon_use_admonition_for_notes = False
napoleon_use_admonition_for_references = False
napoleon_use_ivar = False
napoleon_use_param = True
napoleon_use_rtype = True
napoleon_preprocess_types = False
napoleon_type_aliases = None
napoleon_attr_annotations = True

# Optional: Set the file suffixes that MyST will handle
source_suffix = {
    ".rst": "restructuredtext",
    ".md": "markdown",
}

# Optionally, ensure that MyST is the default parser for Markdown files
source_parsers = {
    ".md": "myst_parser",
}
# -- Options for HTML output -------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#options-for-html-output

# html_theme = "alabaster"
html_theme = "sphinx_rtd_theme"
html_static_path = ["_static"]


def setup(app):
    from theorem_index import TheoremIndex

    app.add_directive("theorem-index", TheoremIndex)
    app.add_js_file("theorem-search.js", loading_method="defer")
