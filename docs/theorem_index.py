"""Render theorem statements and attach symbol search data."""

import json
from html import escape
from importlib import import_module
from pathlib import Path

from docutils import nodes
from sphinx.util.docutils import SphinxDirective

from lite.cells import Definitions, repl_url, skipped, theorem_modules

_SOURCE = "https://github.com/philzook58/knuckledragger/blob/main"
_ROOT = Path(__file__).resolve().parents[1]


def _proofs(module):
    """Public proofs bound in `module`, sorted by name."""
    from kdrag import Proof

    return [
        (name, proof)
        for name, proof in sorted(vars(module).items())
        if not name.startswith("_") and isinstance(proof, Proof)
    ]


class TheoremIndex(SphinxDirective):
    optional_arguments = 1

    def run(self):
        modules = [
            Definitions(import_module(name))
            for name in self.arguments or theorem_modules()
        ]
        # An imported proof is listed only where it is defined, if that module is listed.
        defined = {
            proof.thm.get_id()
            for defs in modules
            for name, proof in _proofs(defs.module)
            if name in defs.lines
        }
        rows = [row for defs in modules for row in self.statements(defs, defined)]
        if not rows:
            return []
        table = nodes.table(classes=["theorem-table"])
        labels = ["Theorem", "Statement"] + ([""] if self.config.theorem_lite_url else [])
        group = nodes.tgroup(cols=len(labels))
        for width in (24, 74, 2)[: len(labels)]:
            group += nodes.colspec(colwidth=width)
        header = nodes.row()
        for label in labels:
            header += nodes.entry("", nodes.paragraph(text=label))
        group += nodes.thead("", header)
        group += nodes.tbody("", *rows)
        table += group
        return [table]

    def statements(self, defs, defined):
        from kdrag import pretty_expr
        from kdrag.utils import decls

        module = defs.module
        module_name = module.__name__
        source = Path(module.__file__)
        self.env.note_dependency(str(source))
        source_url = f"{_SOURCE}/{source.relative_to(_ROOT).as_posix()}"
        lines = defs.lines
        skip = skipped()
        entries = []
        for name, proof in _proofs(module):
            if name not in lines and proof.thm.get_id() in defined:
                continue
            qualified_name = f"{module_name}.{name}"
            entry = nodes.row(
                ids=[nodes.make_id(qualified_name)], classes=["theorem-entry"]
            )
            title = nodes.paragraph()
            url = f"{source_url}#L{lines[name]}" if name in lines else source_url
            display_name = qualified_name.removeprefix("kdrag.theories.").removeprefix(
                "kdrag."
            )
            title += nodes.reference(
                "", "", nodes.literal(text=display_name), refuri=url
            )
            if proof.admit:
                title += nodes.Text(" (admitted)")
            statement = pretty_expr(proof.thm, width=60)
            entry += nodes.entry("", title)
            symbols = sorted({str(decl.name()) for decl in decls(proof.thm)})
            data = escape(json.dumps([qualified_name, symbols]), quote=True)
            metadata = nodes.raw(
                "", f'<span hidden data-theorem="{data}"></span>', format="html"
            )
            entry += nodes.entry(
                "",
                nodes.paragraph(
                    "",
                    "",
                    nodes.literal(
                        text=statement,
                        classes=["theorem-formula"],
                    ),
                ),
                metadata,
            )
            if lite := self.config.theorem_lite_url:
                link = nodes.raw("", "", format="html")
                if not {qualified_name, module_name} & skip:
                    href = escape(repl_url(lite, defs.cell(name)), quote=True)
                    link = nodes.raw(
                        "",
                        f'<a class="theorem-try" href="{href}" target="_blank"'
                        ' title="Edit and rerun in the browser">'
                        f'<img src="{lite}/icon-120x120.png" alt="try"></a>',
                        format="html",
                    )
                entry += nodes.entry("", link)
            self.state.document.note_explicit_target(entry)
            entries.append(entry)
        return entries
