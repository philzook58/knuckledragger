"""Render public proof bindings from the modules listed on a documentation page."""

from html import escape
from importlib import import_module
import json

from docutils import nodes
from sphinx.util.docutils import SphinxDirective


class TheoremIndex(SphinxDirective):
    required_arguments = 1

    def run(self):
        from kdrag import Proof, pretty_expr
        from kdrag.utils import decls

        module = import_module(self.arguments[0])
        self.env.note_dependency(module.__file__)
        entries = []
        for name, proof in sorted(vars(module).items()):
            if name.startswith("_") or not isinstance(proof, Proof):
                continue
            qualified_name = f"{module.__name__}.{name}"
            anchor = nodes.make_id(qualified_name)
            entry = nodes.section(ids=[anchor])
            entry += nodes.title(text=name)
            if proof.admit:
                entry += nodes.paragraph(text="Admitted.")
            entry += nodes.literal_block(text=pretty_expr(proof.thm))
            symbols = sorted({str(decl.name()) for decl in decls(proof.thm)})
            data = escape(json.dumps([qualified_name, symbols]), quote=True)
            entry += nodes.raw(
                "", f'<span hidden data-theorem="{data}"></span>', format="html"
            )
            self.state.document.note_explicit_target(entry)
            entries.append(entry)
        return entries
