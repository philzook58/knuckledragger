"""Render theorem statements and attach symbol search data."""

import json
from html import escape
from importlib import import_module

from docutils import nodes
from sphinx.util.docutils import SphinxDirective

_STATEMENT_MODULES = {"int", "nat", "real", "real.analysis", "real.cont", "real.seq"}


class TheoremIndex(SphinxDirective):
    optional_arguments = 1

    def run(self):
        if self.arguments:
            module_name = self.arguments[0]
            if module_name.removeprefix("kdrag.theories.") in _STATEMENT_MODULES:
                return self.statements(module_name)
            return []
        return [
            entry
            for name in sorted(_STATEMENT_MODULES)
            for entry in self.statements(f"kdrag.theories.{name}")
        ]

    def statements(self, module_name):
        from kdrag import Proof, pretty_expr
        from kdrag.utils import decls

        module = import_module(module_name)
        self.env.note_dependency(module.__file__)
        entries = []
        for name, proof in sorted(vars(module).items()):
            if name.startswith("_") or not isinstance(proof, Proof):
                continue
            qualified_name = f"{module_name}.{name}"
            entry = nodes.container(
                ids=[nodes.make_id(qualified_name)], classes=["theorem-entry"]
            )
            title = nodes.paragraph()
            title += nodes.literal(text=name)
            if proof.admit:
                title += nodes.Text(" (admitted)")
            entry += title
            entry += nodes.literal_block(text=pretty_expr(proof.thm))
            symbols = sorted({str(decl.name()) for decl in decls(proof.thm)})
            data = escape(json.dumps([qualified_name, symbols]), quote=True)
            entry += nodes.raw(
                "", f'<span hidden data-theorem="{data}"></span>', format="html"
            )
            self.state.document.note_explicit_target(entry)
            entries.append(entry)
        return entries
