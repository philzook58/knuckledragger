"""Render the theory module tree and statements from selected modules."""

import json
from html import escape
from importlib import import_module
from pathlib import Path

from docutils import nodes
from sphinx.util.docutils import SphinxDirective

_THEORIES = Path(__file__).resolve().parents[1] / "src/kdrag/theories"
_STATEMENT_MODULES = {"int", "nat", "real", "real.analysis", "real.cont", "real.seq"}
_SOURCE = "https://github.com/philzook58/knuckledragger/blob/main/src/kdrag/theories"


class TheoremIndex(SphinxDirective):
    def run(self):
        return self.modules(_THEORIES)

    def modules(self, directory, prefix=""):
        self.env.note_dependency(str(directory))
        sections = []
        for path in sorted(directory.iterdir(), key=lambda path: path.stem):
            package = path.is_dir() and (path / "__init__.py").is_file()
            if not package and (path.suffix != ".py" or path.name == "__init__.py"):
                continue
            name = prefix + path.stem
            qualified_name = f"kdrag.theories.{name}"
            section = nodes.section(ids=[nodes.make_id(qualified_name)])
            section += nodes.title(text=path.stem)
            source = path / "__init__.py" if package else path
            url = f"{_SOURCE}/{source.relative_to(_THEORIES).as_posix()}"
            section += nodes.paragraph("", "", nodes.reference(text="Source", refuri=url))
            self.state.document.note_explicit_target(section)
            if name in _STATEMENT_MODULES:
                section.extend(self.statements(qualified_name))
            if package:
                section.extend(self.modules(path, name + "."))
            sections.append(section)
        return sections

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
