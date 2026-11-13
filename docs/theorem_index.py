"""Render public proof bindings from the modules listed on a documentation page."""

from importlib import import_module

from docutils import nodes
from sphinx.util.docutils import SphinxDirective


class TheoremIndex(SphinxDirective):
    required_arguments = 1

    def run(self):
        from kdrag import Proof, pretty_expr

        module = import_module(self.arguments[0])
        self.env.note_dependency(module.__file__)
        entries = []
        for name, proof in sorted(vars(module).items()):
            if name.startswith("_") or not isinstance(proof, Proof):
                continue
            qualified_name = f"{module.__name__}.{name}"
            entry = nodes.section(ids=[nodes.make_id(qualified_name)])
            entry += nodes.title(text=name)
            if proof.admit:
                entry += nodes.paragraph(text="Admitted.")
            entry += nodes.literal_block(text=pretty_expr(proof.thm))
            self.state.document.note_explicit_target(entry)
            entries.append(entry)
        return entries
