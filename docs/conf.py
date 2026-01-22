# Configuration file for the Sphinx documentation builder.
#
# For the full list of built-in configuration values, see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html
import os
import sys
# -- Project information -----------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#project-information

project = "knuckledragger"
copyright = "2024, Philip Zucker"
author = "Philip Zucker"
release = "0.1"

# -- General configuration ---------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#general-configuration


sys.path.insert(0, os.path.abspath(".."))  # Source code dir relative to this file

extensions = [
    "sphinx.ext.duration",
    "sphinx.ext.doctest",
    "sphinx.ext.autodoc",
    "sphinx.ext.autosummary",
    "sphinx.ext.napoleon",
    "myst_parser",
]
autosummary_generate = True

autodoc_default_options = {
    "members": True,
    "undoc-members": True,  # Include undocumented members
    "inherited-members": True,
    "show-inheritance": True,
    "member-order": "bysource",  # Keep source order
    "special-members": False,  # Don't show __special__ methods
}

# Enable documenting module-level data/attributes
autodoc_member_order = 'bysource'
autodoc_class_signature = 'separated'

# Include module-level attributes (like Proof objects)
# This ensures that module-level variables are documented
automodule_include_private = False
autodata_content = "both"

# Disable autodoc typehints to avoid conflicts with Z3's custom __eq__
autodoc_typehints = "none"
autodoc_typehints_format = "short"

# Setup function to monkey-patch Z3's __eq__ to work with Sphinx and customize autosummary
def setup(app):
    """Monkey-patch Z3's custom __eq__ methods and customize autosummary for Proof objects."""
    import kdrag.smt as smt
    import kdrag as kd
    
    # Store original eq function
    _original_eq = smt.eq
    
    # Create a safer version that checks if both objects have get_id
    def safe_eq(x, y):
        """Safe equality that handles non-Z3 objects."""
        try:
            # Only use get_id if both objects have it
            if hasattr(x, 'get_id') and hasattr(y, 'get_id') and callable(x.get_id):
                return x.get_id() == y.get_id()
            # Fall back to normal Python equality
            return x is y
        except (AttributeError, TypeError):
            return x is y
    
    # Replace the eq method on the classes
    smt.SortRef.__eq__ = safe_eq
    smt.FuncDeclRef.__eq__ = safe_eq
    smt.SortRef.__ne__ = lambda x, y: not safe_eq(x, y)
    smt.FuncDeclRef.__ne__ = lambda x, y: not safe_eq(x, y)
    
    # Custom autosummary member collection to include Proof objects
    from sphinx.ext.autosummary import get_documenter, Autosummary
    from sphinx.ext.autodoc import DataDocumenter, ModuleDocumenter
    import importlib
    
    # Custom ModuleDocumenter that includes Proof objects
    from sphinx.ext.autodoc import ModuleDocumenter as OrigModuleDocumenter
    
    class ProofAwareModuleDocumenter(OrigModuleDocumenter):
        """Module documenter that includes Proof objects."""
        
        def filter_members(self, members, want_all):
            """Override to include Proof objects."""
            ret = super().filter_members(members, want_all)
            
            # Add Proof objects explicitly
            if hasattr(self.object, '__dict__'):
                for name, obj in self.object.__dict__.items():
                    if not name.startswith('_') and isinstance(obj, kd.Proof):
                        # Add as a data member
                        if not any(n == name for n, *_ in ret):
                            ret.append((name, obj, False))
            
            return ret
    
    # Register the custom documenter
    app.add_autodocumenter(ProofAwareModuleDocumenter, override=True)
    
    # Add post-processing of RST files to add Proof objects after autosummary generates them
    def process_rst_for_proofs(app, env, docnames):
        """Post-process generated RST files to add Proof objects after autosummary."""
        import sys
        from pathlib import Path
        
        # Run the post-processing script
        script_path = Path(app.srcdir) / 'add_proofs_to_rst.py'
        if script_path.exists():
            import subprocess
            result = subprocess.run([sys.executable, str(script_path)], 
                                  cwd=app.srcdir, 
                                  capture_output=True, 
                                  text=True)
            if result.stdout:
                print(result.stdout)
    
    app.connect('env-before-read-docs', process_rst_for_proofs)


templates_path = ["_templates"]
exclude_patterns = ["_build", "Thumbs.db", ".DS_Store"]

# Suppress warnings from autodoc when dealing with Z3's custom __eq__
suppress_warnings = [
    'autodoc',
    'autodoc.import_object',
]

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
