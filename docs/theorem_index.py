"""Render theorem statements and attach symbol search data."""

import json
from html import escape
from importlib import import_module
from pathlib import Path

from docutils import nodes
from sphinx.util.docutils import SphinxDirective

from lite.cells import Definitions, repl_url, skipped

_SOURCE = "https://github.com/philzook58/knuckledragger/blob/main"
_ROOT = Path(__file__).resolve().parents[1]
_THEORIES = _ROOT / "src/kdrag/theories"


class TheoremIndex(SphinxDirective):
    optional_arguments = 1

    def run(self):
        modules = self.arguments or [
            ".".join(path.relative_to(_ROOT / "src").with_suffix("").parts)
            .removesuffix(".__init__")
            for path in sorted(_THEORIES.rglob("*.py"))
        ]
        rows = [row for module in modules for row in self.statements(module)]
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

    def statements(self, module_name):
        from kdrag import Proof, pretty_expr
        from kdrag.utils import decls

        module = import_module(module_name)
        source = Path(module.__file__)
        self.env.note_dependency(str(source))
        source_url = f"{_SOURCE}/{source.relative_to(_ROOT).as_posix()}"
        defs = Definitions(module)
        lines = defs.lines
        skip = skipped()
        entries = []
        for name, proof in sorted(vars(module).items()):
            if name.startswith("_") or not isinstance(proof, Proof):
                continue
            qualified_name = f"{module_name}.{name}"
            entry = nodes.row(
                ids=[nodes.make_id(qualified_name)], classes=["theorem-entry"]
            )
            title = nodes.paragraph()
            url = f"{source_url}#L{lines[name]}" if name in lines else source_url
            display_name = qualified_name.removeprefix("kdrag.theories.")
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
